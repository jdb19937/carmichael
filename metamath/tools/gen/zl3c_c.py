"""ZL3c section C: the Gamma comparison and QBND.  `MM_DB=sorties/zl3c.mm python3 tools/gen/zl3c_c.py LABEL...`"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(__file__))
from zl2lib import W, D, E, a1, Closure, chain, efle_, efadd_
from lin import linarith, nlinarith
import zl3clib as L
from c0lib import runh
from zl1lib import mptv

only = sys.argv[1:]


def go(w):
    if only and w.label not in only:
        return True
    if os.environ.get('ZL3C_WRITE'):
        w.write(); print('WROTE', w.label, len(w.lines)); return True
    return runh(w) if L.HYPS.get(w.label) else w.run()


def want(label):
    return not only or label in only


def ante_of(label):
    s = L.STATEMENTS[label]
    body = s[2:-2]
    # split top-level ' -> '
    depth = 0; toks = body.split(' ')
    for i, t in enumerate(toks):
        if t == '(':
            depth += 1
        elif t == ')':
            depth -= 1
        elif t == '->' and depth == 0:
            return ' '.join(toks[:i]), ' '.join(toks[i + 1:])
    raise ValueError(label)


# ---------------------------------------------------------------- zl3rab
if __name__ == '__main__' and want('zl3rab'):
    w = W('zl3rab', 'Two complex numbers with the same absolute imaginary part and real parts ` 0 < Re A <_ Re B ` : '
          'the ratio ` Re / abs ` increases with the real part.  The factor comparison behind ~ zl3gmono .')
    A, C = ante_of('zl3rab')
    ac = D(w, A, 'simpll', [], 'A e. CC'); bc = D(w, A, 'simplr', [], 'B e. CC')
    hh = D(w, A, 'simpr', [], '( ( abs ` ( Im ` A ) ) = ( abs ` ( Im ` B ) ) /\\ 0 < ( Re ` A ) /\\ ( Re ` A ) <_ ( Re ` B ) )')
    ei = D(w, A, 'simp1d', [hh], '( abs ` ( Im ` A ) ) = ( abs ` ( Im ` B ) )')
    a0 = D(w, A, 'simp2d', [hh], '0 < ( Re ` A )')
    ab = D(w, A, 'simp3d', [hh], '( Re ` A ) <_ ( Re ` B )')
    a, b, p, q = '( Re ` A )', '( Re ` B )', '( Im ` A )', '( Im ` B )'
    aA, aB = '( abs ` A )', '( abs ` B )'
    ar = D(w, A, 'recld', [ac], '%s e. RR' % a); br = D(w, A, 'recld', [bc], '%s e. RR' % b)
    pr = D(w, A, 'imcld', [ac], '%s e. RR' % p); qr = D(w, A, 'imcld', [bc], '%s e. RR' % q)
    aAr = D(w, A, 'abscld', [ac], '%s e. RR' % aA); aBr = D(w, A, 'abscld', [bc], '%s e. RR' % aB)
    aA0 = D(w, A, 'absge0d', [ac], '0 <_ %s' % aA); aB0 = D(w, A, 'absge0d', [bc], '0 <_ %s' % aB)
    cl = Closure(w, A, {a: ('RR', ar), b: ('RR', br), q: ('RR', qr), aA: ('RR', aAr), aB: ('RR', aBr)})
    a0le = linarith(w, A, [a0], '0 <_ %s' % a, closure=cl)
    b0le = linarith(w, A, [a0, ab], '0 <_ %s' % b, closure=cl)
    # p^2 = q^2
    pq = w.s([w.s([pr, qr, w.inst('sqabs')], 'syl2anc', '( %s -> ( ( %s ^ 2 ) = ( %s ^ 2 ) <-> ( abs ` %s ) = ( abs ` %s ) ) )' % (A, p, q, p, q)), ei],
             'mpbird', '( %s -> ( %s ^ 2 ) = ( %s ^ 2 ) )' % (A, p, q))
    eA = w.s([ac, w.inst('absvalsq2')], 'syl', '( %s -> ( %s ^ 2 ) = ( ( %s ^ 2 ) + ( %s ^ 2 ) ) )' % (A, aA, a, p))
    eB = w.s([bc, w.inst('absvalsq2')], 'syl', '( %s -> ( %s ^ 2 ) = ( ( %s ^ 2 ) + ( %s ^ 2 ) ) )' % (A, aB, b, q))
    eA2 = E(w, A, 'oveq2d', [pq], '( ( %s ^ 2 ) + ( %s ^ 2 ) )' % (a, p), '( ( %s ^ 2 ) + ( %s ^ 2 ) )' % (a, q))
    eA3 = w.s([eA, eA2], 'eqtrd', '( %s -> ( %s ^ 2 ) = ( ( %s ^ 2 ) + ( %s ^ 2 ) ) )' % (A, aA, a, q))
    acc = D(w, A, 'recnd', [ar], '%s e. CC' % a); bcc = D(w, A, 'recnd', [br], '%s e. CC' % b)
    aAc = D(w, A, 'recnd', [aAr], '%s e. CC' % aA); aBc = D(w, A, 'recnd', [aBr], '%s e. CC' % aB)
    L1 = '( %s x. %s )' % (a, aB); R1 = '( %s x. %s )' % (b, aA)
    s1 = E(w, A, 'sqmuld', [acc, aBc], '( %s ^ 2 )' % L1, '( ( %s ^ 2 ) x. ( %s ^ 2 ) )' % (a, aB))
    s1b = E(w, A, 'oveq2d', [eB], '( ( %s ^ 2 ) x. ( %s ^ 2 ) )' % (a, aB), '( ( %s ^ 2 ) x. ( ( %s ^ 2 ) + ( %s ^ 2 ) ) )' % (a, b, q))
    s2 = E(w, A, 'sqmuld', [bcc, aAc], '( %s ^ 2 )' % R1, '( ( %s ^ 2 ) x. ( %s ^ 2 ) )' % (b, aA))
    s2b = E(w, A, 'oveq2d', [eA3], '( ( %s ^ 2 ) x. ( %s ^ 2 ) )' % (b, aA), '( ( %s ^ 2 ) x. ( ( %s ^ 2 ) + ( %s ^ 2 ) ) )' % (b, a, q))
    sq = w.s([w.s([ar, br, a0le, b0le], 'le2sqd', '( %s -> ( %s <_ %s <-> ( %s ^ 2 ) <_ ( %s ^ 2 ) ) )' % (A, a, b, a, b)), ab],
             'mpbid', '( %s -> ( %s ^ 2 ) <_ ( %s ^ 2 ) )' % (A, a, b))
    q2 = D(w, A, 'sqge0d', [qr], '0 <_ ( %s ^ 2 )' % q)
    core = nlinarith(w, A, [sq, q2], '( ( %s ^ 2 ) x. ( ( %s ^ 2 ) + ( %s ^ 2 ) ) ) <_ ( ( %s ^ 2 ) x. ( ( %s ^ 2 ) + ( %s ^ 2 ) ) )' % (a, b, q, b, a, q), closure=cl)
    l1 = w.s([s1, s1b], 'eqtrd', '( %s -> ( %s ^ 2 ) = ( ( %s ^ 2 ) x. ( ( %s ^ 2 ) + ( %s ^ 2 ) ) ) )' % (A, L1, a, b, q))
    r1 = w.s([s2, s2b], 'eqtrd', '( %s -> ( %s ^ 2 ) = ( ( %s ^ 2 ) x. ( ( %s ^ 2 ) + ( %s ^ 2 ) ) ) )' % (A, R1, b, a, q))
    c1 = w.s([l1, core], 'eqbrtrd', '( %s -> ( %s ^ 2 ) <_ ( ( %s ^ 2 ) x. ( ( %s ^ 2 ) + ( %s ^ 2 ) ) ) )' % (A, L1, b, a, q))
    c2 = w.s([c1, r1], 'breqtrrd', '( %s -> ( %s ^ 2 ) <_ ( %s ^ 2 ) )' % (A, L1, R1))
    L1r = D(w, A, 'remulcld', [ar, aBr], '%s e. RR' % L1); R1r = D(w, A, 'remulcld', [br, aAr], '%s e. RR' % R1)
    L10 = D(w, A, 'mulge0d', [ar, aBr, a0le, aB0], '0 <_ %s' % L1); R10 = D(w, A, 'mulge0d', [br, aAr, b0le, aA0], '0 <_ %s' % R1)
    w.qed([c2, w.s([L1r, R1r, L10, R10], 'le2sqd', '( %s -> ( %s <_ %s <-> ( %s ^ 2 ) <_ ( %s ^ 2 ) ) )' % (A, L1, R1, L1, R1))],
          'mpbird', L.STATEMENTS['zl3rab'])
    go(w)


def den(w, A, Z, zc, mr, mrp, mc, mne, zpos):
    """facts about DEN = ( ( Z / M ) + 1 ) and XDEN = ( ( ( Re ` Z ) / M ) + 1 ):
    Re DEN = XDEN, ( abs ` ( Im ` DEN ) ) = ( ( abs ` ( Im ` Z ) ) / M ), XDEN e. RR+, DEN e. CC, ( abs ` DEN ) e. RR+"""
    DN = '( ( %s / M ) + 1 )' % Z
    X = '( ( ( Re ` %s ) / M ) + 1 )' % Z
    c1 = a1(w, A, 'ax-1cn', '1 e. CC')
    zm = D(w, A, 'divcld', [zc, mc, mne], '( %s / M ) e. CC' % Z)
    dc = D(w, A, 'addcld', [zm, c1], '%s e. CC' % DN)
    zr = D(w, A, 'recld', [zc], '( Re ` %s ) e. RR' % Z)
    re1 = E(w, A, 'readdd', [zm, c1], '( Re ` %s )' % DN, '( ( Re ` ( %s / M ) ) + ( Re ` 1 ) )' % Z)
    re2 = E(w, A, 'redivd', [mr, zc, mne], '( Re ` ( %s / M ) )' % Z, '( ( Re ` %s ) / M )' % Z)
    re3 = w.s([w.s([], 're1', '( Re ` 1 ) = 1')], 'a1i', '( %s -> ( Re ` 1 ) = 1 )' % A)
    re4 = E(w, A, 'oveq12d', [re2, re3], '( ( Re ` ( %s / M ) ) + ( Re ` 1 ) )' % Z, X)
    reD = w.s([re1, re4], 'eqtrd', '( %s -> ( Re ` %s ) = %s )' % (A, DN, X))
    im1 = E(w, A, 'imaddd', [zm, c1], '( Im ` %s )' % DN, '( ( Im ` ( %s / M ) ) + ( Im ` 1 ) )' % Z)
    im2 = E(w, A, 'imdivd', [mr, zc, mne], '( Im ` ( %s / M ) )' % Z, '( ( Im ` %s ) / M )' % Z)
    im3 = w.s([w.s([], 'im1', '( Im ` 1 ) = 0')], 'a1i', '( %s -> ( Im ` 1 ) = 0 )' % A)
    im4 = E(w, A, 'oveq12d', [im2, im3], '( ( Im ` ( %s / M ) ) + ( Im ` 1 ) )' % Z, '( ( ( Im ` %s ) / M ) + 0 )' % Z)
    izr = D(w, A, 'imcld', [zc], '( Im ` %s ) e. RR' % Z)
    izm = D(w, A, 'redivcld', [izr, mr, mne], '( ( Im ` %s ) / M ) e. RR' % Z)
    im5 = E(w, A, 'addridd', [D(w, A, 'recnd', [izm], '( ( Im ` %s ) / M ) e. CC' % Z)], '( ( ( Im ` %s ) / M ) + 0 )' % Z, '( ( Im ` %s ) / M )' % Z)
    imD = chain(w, A, ['( Im ` %s )' % DN, '( ( Im ` ( %s / M ) ) + ( Im ` 1 ) )' % Z, '( ( ( Im ` %s ) / M ) + 0 )' % Z, '( ( Im ` %s ) / M )' % Z], [im1, im4, im5])
    a1_ = E(w, A, 'fveq2d', [imD], '( abs ` ( Im ` %s ) )' % DN, '( abs ` ( ( Im ` %s ) / M ) )' % Z)
    a2_ = E(w, A, 'absdivd', [D(w, A, 'recnd', [izr], '( Im ` %s ) e. CC' % Z), mc, mne], '( abs ` ( ( Im ` %s ) / M ) )' % Z, '( ( abs ` ( Im ` %s ) ) / ( abs ` M ) )' % Z)
    a3_ = E(w, A, 'oveq2d', [E(w, A, 'absidd', [mr, D(w, A, 'rpge0d', [mrp], '0 <_ M')], '( abs ` M )', 'M')],
            '( ( abs ` ( Im ` %s ) ) / ( abs ` M ) )' % Z, '( ( abs ` ( Im ` %s ) ) / M )' % Z)
    absIm = chain(w, A, ['( abs ` ( Im ` %s ) )' % DN, '( abs ` ( ( Im ` %s ) / M ) )' % Z, '( ( abs ` ( Im ` %s ) ) / ( abs ` M ) )' % Z, '( ( abs ` ( Im ` %s ) ) / M )' % Z], [a1_, a2_, a3_])
    zrp = D(w, A, 'elrpd', [zr, zpos], '( Re ` %s ) e. RR+' % Z)
    xrp = D(w, A, 'rpaddcld', [D(w, A, 'rpdivcld', [zrp, mrp], '( ( Re ` %s ) / M ) e. RR+' % Z), a1(w, A, '1rp', '1 e. RR+')], '%s e. RR+' % X)
    xle = w.s([w.s([dc, w.inst('releabs')], 'syl', '( %s -> ( Re ` %s ) <_ ( abs ` %s ) )' % (A, DN, DN)), reD], 'eqbrtrrd', '( %s -> %s <_ ( abs ` %s ) )' % (A, X, DN))
    adr = D(w, A, 'abscld', [dc], '( abs ` %s ) e. RR' % DN)
    apos = D(w, A, 'ltletrd', [a1(w, A, '0re', '0 e. RR'), D(w, A, 'rpred', [xrp], '%s e. RR' % X), adr, D(w, A, 'rpgt0d', [xrp], '0 < %s' % X), xle], '0 < ( abs ` %s )' % DN)
    arp = D(w, A, 'elrpd', [adr, apos], '( abs ` %s ) e. RR+' % DN)
    return dict(DN=DN, X=X, dc=dc, reD=reD, absIm=absIm, xrp=xrp, arp=arp, zr=zr, zrp=zrp)


# ---------------------------------------------------------------- zl3eutc
if __name__ == '__main__' and want('zl3eutc'):
    w = W('zl3eutc', "One factor of Euler's product ( ~ gamcvg2 ) at two points with the same absolute imaginary part: "
          'the modulus relative to the value at the real part increases with the real part ( ~ zl3rab at ` Z / M + 1 ` , ` V / M + 1 ` ).')
    A, C = ante_of('zl3eutc')
    h = D(w, A, 'simpl', [], L.HZV)
    zc = D(w, A, 'simplll', [], 'Z e. CC'); vc = D(w, A, 'simpllr', [], 'V e. CC')
    hh = D(w, A, 'simplr', [], '( ( abs ` ( Im ` Z ) ) = ( abs ` ( Im ` V ) ) /\\ 0 < ( Re ` Z ) /\\ ( Re ` Z ) <_ ( Re ` V ) )')
    ei = D(w, A, 'simp1d', [hh], '( abs ` ( Im ` Z ) ) = ( abs ` ( Im ` V ) )')
    z0 = D(w, A, 'simp2d', [hh], '0 < ( Re ` Z )')
    zv = D(w, A, 'simp3d', [hh], '( Re ` Z ) <_ ( Re ` V )')
    mn = D(w, A, 'simpr', [], 'M e. NN')
    mr = D(w, A, 'nnred', [mn], 'M e. RR'); mrp = D(w, A, 'nnrpd', [mn], 'M e. RR+')
    mc = D(w, A, 'rpcnd', [mrp], 'M e. CC'); mne = D(w, A, 'rpne0d', [mrp], 'M =/= 0')
    zr0 = D(w, A, 'recld', [zc], '( Re ` Z ) e. RR'); vr0 = D(w, A, 'recld', [vc], '( Re ` V ) e. RR')
    v0 = D(w, A, 'ltletrd', [a1(w, A, '0re', '0 e. RR'), zr0, vr0, z0, zv], '0 < ( Re ` V )')
    dz = den(w, A, 'Z', zc, mr, mrp, mc, mne, z0)
    dv = den(w, A, 'V', vc, mr, mrp, mc, mne, v0)
    # the zl3rab instance at A := DZ, B := DV
    eqi = w.s([dz['absIm'], w.s([dv['absIm'], E(w, A, 'oveq1d', [ei], '( ( abs ` ( Im ` Z ) ) / M )', '( ( abs ` ( Im ` V ) ) / M )')], 'eqtr4d',
                                 '( %s -> ( ( abs ` ( Im ` Z ) ) / M ) = ( abs ` ( Im ` %s ) ) )' % (A, dv['DN']))], 'eqtrd',
              '( %s -> ( abs ` ( Im ` %s ) ) = ( abs ` ( Im ` %s ) ) )' % (A, dz['DN'], dv['DN']))
    rz0 = w.s([D(w, A, 'rpgt0d', [dz['xrp']], '0 < %s' % dz['X']), dz['reD']], 'breqtrrd', '( %s -> 0 < ( Re ` %s ) )' % (A, dz['DN']))
    xle = D(w, A, 'leadd1dd', [D(w, A, 'redivcld', [zr0, mr, mne], '( ( Re ` Z ) / M ) e. RR'), D(w, A, 'redivcld', [vr0, mr, mne], '( ( Re ` V ) / M ) e. RR'),
                               a1(w, A, '1re', '1 e. RR'), D(w, A, 'lediv1dd', [zr0, vr0, mrp, zv], '( ( Re ` Z ) / M ) <_ ( ( Re ` V ) / M )')],
            '%s <_ %s' % (dz['X'], dv['X']))
    rle = w.s([w.s([dz['reD'], xle], 'eqbrtrd', '( %s -> ( Re ` %s ) <_ %s )' % (A, dz['DN'], dv['X'])), dv['reD']], 'breqtrrd',
              '( %s -> ( Re ` %s ) <_ ( Re ` %s ) )' % (A, dz['DN'], dv['DN']))
    RAB = '( ( %s e. CC /\\ %s e. CC ) /\\ ( ( abs ` ( Im ` %s ) ) = ( abs ` ( Im ` %s ) ) /\\ 0 < ( Re ` %s ) /\\ ( Re ` %s ) <_ ( Re ` %s ) ) )' % (
        dz['DN'], dv['DN'], dz['DN'], dv['DN'], dz['DN'], dz['DN'], dv['DN'])
    rabh = w.s([w.s([dz['dc'], dv['dc']], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A, dz['DN'], dv['DN'])),
                w.s([eqi, rz0, rle], '3jca', '( %s -> ( ( abs ` ( Im ` %s ) ) = ( abs ` ( Im ` %s ) ) /\\ 0 < ( Re ` %s ) /\\ ( Re ` %s ) <_ ( Re ` %s ) ) )' % (
                    A, dz['DN'], dv['DN'], dz['DN'], dz['DN'], dv['DN']))], 'jca', '( %s -> %s )' % (A, RAB))
    aZ, aV = '( abs ` %s )' % dz['DN'], '( abs ` %s )' % dv['DN']
    rab = w.s([rabh, w.inst('zl3rab')], 'syl', '( %s -> ( ( Re ` %s ) x. %s ) <_ ( ( Re ` %s ) x. %s ) )' % (A, dz['DN'], aV, dv['DN'], aZ))
    e1 = E(w, A, 'oveq1d', [dz['reD']], '( ( Re ` %s ) x. %s )' % (dz['DN'], aV), '( %s x. %s )' % (dz['X'], aV))
    e2 = E(w, A, 'oveq1d', [dv['reD']], '( ( Re ` %s ) x. %s )' % (dv['DN'], aZ), '( %s x. %s )' % (dv['X'], aZ))
    rab2 = w.s([w.s([e1, rab], 'eqbrtrrd', '( %s -> ( %s x. %s ) <_ ( ( Re ` %s ) x. %s ) )' % (A, dz['X'], aV, dv['DN'], aZ)), e2], 'breqtrd',
               '( %s -> ( %s x. %s ) <_ ( %s x. %s ) )' % (A, dz['X'], aV, dv['X'], aZ))
    # values
    NZ = '( ( ( M + 1 ) / M ) ^c ( Re ` Z ) )'; NV = '( ( ( M + 1 ) / M ) ^c ( Re ` V ) )'
    m1 = D(w, A, 'rpdivcld', [D(w, A, 'rpaddcld', [mrp, a1(w, A, '1rp', '1 e. RR+')], '( M + 1 ) e. RR+'), mrp], '( ( M + 1 ) / M ) e. RR+')
    nz = D(w, A, 'rpcxpcld', [m1, zr0], '%s e. RR+' % NZ); nv = D(w, A, 'rpcxpcld', [m1, vr0], '%s e. RR+' % NV)
    zp = w.s([zc, z0], 'jca', '( %s -> ( Z e. CC /\\ 0 < ( Re ` Z ) ) )' % A)
    vp = w.s([vc, v0], 'jca', '( %s -> ( V e. CC /\\ 0 < ( Re ` V ) ) )' % A)
    eZ = w.s([zp, mn, w.inst('eutabs')], 'syl2anc', '( %s -> ( abs ` ( %s ` M ) ) = ( %s / %s ) )' % (A, L.EUT('Z'), NZ, aZ))
    eV = w.s([vp, mn, w.inst('eutabs')], 'syl2anc', '( %s -> ( abs ` ( %s ` M ) ) = ( %s / %s ) )' % (A, L.EUT('V'), NV, aV))
    xZ = w.s([mn, w.inst('eutval')], 'syl', '( %s -> ( %s ` M ) = ( %s / %s ) )' % (A, L.EUT('( Re ` Z )'), NZ, dz['X']))
    xV = w.s([mn, w.inst('eutval')], 'syl', '( %s -> ( %s ` M ) = ( %s / %s ) )' % (A, L.EUT('( Re ` V )'), NV, dv['X']))
    LHS = '( ( abs ` ( %s ` M ) ) x. ( %s ` M ) )' % (L.EUT('Z'), L.EUT('( Re ` V )'))
    RHS = '( ( abs ` ( %s ` M ) ) x. ( %s ` M ) )' % (L.EUT('V'), L.EUT('( Re ` Z )'))
    def rpc(st, t):
        return D(w, A, 'rpcnd', [st], '%s e. CC' % t)
    def rpn(st, t):
        return D(w, A, 'rpne0d', [st], '%s =/= 0' % t)
    l1 = E(w, A, 'oveq12d', [eZ, xV], LHS, '( ( %s / %s ) x. ( %s / %s ) )' % (NZ, aZ, NV, dv['X']))
    l2 = E(w, A, 'divmuldivd', [rpc(nz, NZ), rpc(dz['arp'], aZ), rpc(nv, NV), rpc(dv['xrp'], dv['X']), rpn(dz['arp'], aZ), rpn(dv['xrp'], dv['X'])],
           '( ( %s / %s ) x. ( %s / %s ) )' % (NZ, aZ, NV, dv['X']), '( ( %s x. %s ) / ( %s x. %s ) )' % (NZ, NV, aZ, dv['X']))
    r1 = E(w, A, 'oveq12d', [eV, xZ], RHS, '( ( %s / %s ) x. ( %s / %s ) )' % (NV, aV, NZ, dz['X']))
    r2 = E(w, A, 'divmuldivd', [rpc(nv, NV), rpc(dv['arp'], aV), rpc(nz, NZ), rpc(dz['xrp'], dz['X']), rpn(dv['arp'], aV), rpn(dz['xrp'], dz['X'])],
           '( ( %s / %s ) x. ( %s / %s ) )' % (NV, aV, NZ, dz['X']), '( ( %s x. %s ) / ( %s x. %s ) )' % (NV, NZ, aV, dz['X']))
    r3 = E(w, A, 'oveq1d', [E(w, A, 'mulcomd', [rpc(nv, NV), rpc(nz, NZ)], '( %s x. %s )' % (NV, NZ), '( %s x. %s )' % (NZ, NV))],
           '( ( %s x. %s ) / ( %s x. %s ) )' % (NV, NZ, aV, dz['X']), '( ( %s x. %s ) / ( %s x. %s ) )' % (NZ, NV, aV, dz['X']))
    # ( aV x. XZ ) <_ ( aZ x. XV ) from rab2 by commutation
    cm1 = E(w, A, 'mulcomd', [rpc(dz['xrp'], dz['X']), rpc(dv['arp'], aV)], '( %s x. %s )' % (dz['X'], aV), '( %s x. %s )' % (aV, dz['X']))
    cm2 = E(w, A, 'mulcomd', [rpc(dv['xrp'], dv['X']), rpc(dz['arp'], aZ)], '( %s x. %s )' % (dv['X'], aZ), '( %s x. %s )' % (aZ, dv['X']))
    dle = w.s([w.s([cm1, rab2], 'eqbrtrrd', '( %s -> ( %s x. %s ) <_ ( %s x. %s ) )' % (A, aV, dz['X'], dv['X'], aZ)), cm2], 'breqtrd',
              '( %s -> ( %s x. %s ) <_ ( %s x. %s ) )' % (A, aV, dz['X'], aZ, dv['X']))
    PN = '( %s x. %s )' % (NZ, NV)
    pn = D(w, A, 'rpmulcld', [nz, nv], '%s e. RR+' % PN)
    dd = D(w, A, 'lediv2ad', [D(w, A, 'rpmulcld', [dv['arp'], dz['xrp']], '( %s x. %s ) e. RR+' % (aV, dz['X'])),
                              D(w, A, 'rpmulcld', [dz['arp'], dv['xrp']], '( %s x. %s ) e. RR+' % (aZ, dv['X'])),
                              D(w, A, 'rpred', [pn], '%s e. RR' % PN), D(w, A, 'rpge0d', [pn], '0 <_ %s' % PN), dle],
           '( %s / ( %s x. %s ) ) <_ ( %s / ( %s x. %s ) )' % (PN, aZ, dv['X'], PN, aV, dz['X']))
    lhs = w.s([l1, l2], 'eqtrd', '( %s -> %s = ( %s / ( %s x. %s ) ) )' % (A, LHS, PN, aZ, dv['X']))
    rhs = chain(w, A, [RHS, '( ( %s / %s ) x. ( %s / %s ) )' % (NV, aV, NZ, dz['X']), '( ( %s x. %s ) / ( %s x. %s ) )' % (NV, NZ, aV, dz['X']),
                       '( %s / ( %s x. %s ) )' % (PN, aV, dz['X'])], [r1, r2, r3])
    w.qed([w.s([lhs, dd], 'eqbrtrd', '( %s -> %s <_ ( %s / ( %s x. %s ) ) )' % (A, LHS, PN, aV, dz['X'])), rhs], 'breqtrrd', L.STATEMENTS['zl3eutc'])
    go(w)


# ---------------------------------------------------------------- zl3gseq
if __name__ == '__main__' and want('zl3gseq'):
    w = W('zl3gseq', 'The comparison ~ zl3eutc multiplied over the first ` N ` factors of Euler\'s product '
          '( ~ fprodser , ~ fprodabs , ~ fprodmul , ~ fprodle ).')
    A, C = ante_of('zl3gseq')
    FZ = '( 1 ... N )'
    A2 = '( %s /\\ k e. %s )' % (A, FZ)
    A3 = '( %s /\\ k e. ( ZZ>= ` 1 ) )' % A
    zc = D(w, A, 'simplll', [], 'Z e. CC'); vc = D(w, A, 'simpllr', [], 'V e. CC')
    hh = D(w, A, 'simplr', [], '( ( abs ` ( Im ` Z ) ) = ( abs ` ( Im ` V ) ) /\\ 0 < ( Re ` Z ) /\\ ( Re ` Z ) <_ ( Re ` V ) )')
    z0 = D(w, A, 'simp2d', [hh], '0 < ( Re ` Z )')
    zv = D(w, A, 'simp3d', [hh], '( Re ` Z ) <_ ( Re ` V )')
    v0 = D(w, A, 'ltletrd', [a1(w, A, '0re', '0 e. RR'), D(w, A, 'recld', [zc], '( Re ` Z ) e. RR'), D(w, A, 'recld', [vc], '( Re ` V ) e. RR'), z0, zv], '0 < ( Re ` V )')
    zp = w.s([zc, z0], 'jca', '( %s -> ( Z e. CC /\\ 0 < ( Re ` Z ) ) )' % A)
    vp = w.s([vc, v0], 'jca', '( %s -> ( V e. CC /\\ 0 < ( Re ` V ) ) )' % A)
    nn = D(w, A, 'simpr', [], 'N e. NN')
    nuz = w.s([nn, w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'a1i', '( %s -> NN = ( ZZ>= ` 1 ) )' % A)], 'eleqtrd', '( %s -> N e. ( ZZ>= ` 1 ) )' % A)
    T = {'Z': L.EUT('Z'), 'RV': L.EUT('( Re ` V )'), 'V': L.EUT('V'), 'RZ': L.EUT('( Re ` Z )')}

    def ctx(Ak, kin):
        """steps in context Ak: k e. NN, the four factor facts"""
        kn = kin()
        zpk = w.s([w.s([zp], 'adantr', '( %s -> ( Z e. CC /\\ 0 < ( Re ` Z ) ) )' % Ak), kn], 'jca', '( %s -> ( ( Z e. CC /\\ 0 < ( Re ` Z ) ) /\\ k e. NN ) )' % Ak)
        vpk = w.s([w.s([vp], 'adantr', '( %s -> ( V e. CC /\\ 0 < ( Re ` V ) ) )' % Ak), kn], 'jca', '( %s -> ( ( V e. CC /\\ 0 < ( Re ` V ) ) /\\ k e. NN ) )' % Ak)
        f = {}
        f['Z'] = w.s([zpk, w.inst('eutzcl')], 'syl', '( %s -> ( %s ` k ) e. CC )' % (Ak, T['Z']))
        f['V'] = w.s([vpk, w.inst('eutzcl')], 'syl', '( %s -> ( %s ` k ) e. CC )' % (Ak, T['V']))
        f['RV'] = w.s([vpk, w.inst('eutxrp')], 'syl', '( %s -> ( %s ` k ) e. RR+ )' % (Ak, T['RV']))
        f['RZ'] = w.s([zpk, w.inst('eutxrp')], 'syl', '( %s -> ( %s ` k ) e. RR+ )' % (Ak, T['RZ']))
        return kn, f

    kn2, f2 = ctx(A2, lambda: w.s([D(w, A2, 'simpr', [], 'k e. %s' % FZ), w.inst('elfznn')], 'syl', '( %s -> k e. NN )' % A2))
    kn3, f3 = ctx(A3, lambda: w.s([D(w, A3, 'simpr', [], 'k e. ( ZZ>= ` 1 )'), w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'a1i', '( %s -> NN = ( ZZ>= ` 1 ) )' % A3)],
                                     'eleqtrrd', '( %s -> k e. NN )' % A3))
    SQ = lambda key: '( seq 1 ( x. , %s ) ` N )' % T[key]
    PR = lambda t: 'prod_ k e. %s %s' % (FZ, t)
    V = lambda key: '( %s ` k )' % T[key]
    ser = {}
    for key in T:
        cc = f2[key] if key in ('Z', 'V') else D(w, A2, 'rpcnd', [f2[key]], '%s e. CC' % V(key))
        ser[key] = w.s([w.s([], 'eqidd', '( %s -> %s = %s )' % (A2, V(key), V(key))), nuz, cc], 'fprodser', '( %s -> %s = %s )' % (A, PR(V(key)), SQ(key)))
    ab = {}
    for key in ('Z', 'V'):
        pa = w.s([w.s([], 'eqid', '( ZZ>= ` 1 ) = ( ZZ>= ` 1 )'), nuz, f3[key]], 'fprodabs',
                 '( %s -> ( abs ` %s ) = %s )' % (A, PR(V(key)), PR('( abs ` %s )' % V(key))))
        # ( abs ` seq ) = prod abs
        ab[key] = w.s([E(w, A, 'fveq2d', [ser[key]], '( abs ` %s )' % PR(V(key)), '( abs ` %s )' % SQ(key)), pa], 'eqtr3d',
                      '( %s -> ( abs ` %s ) = %s )' % (A, SQ(key), PR('( abs ` %s )' % V(key))))
    fin = w.s([], 'fzfid', '( %s -> %s e. Fin )' % (A, FZ))

    def side(k1, k2):
        """( ante -> ( ( abs ` SQ k1 ) x. SQ k2 ) = prod ( ( abs ` V k1 ) x. V k2 ) )"""
        a1c = D(w, A2, 'abscld', [f2[k1]], '( abs ` %s ) e. RR' % V(k1))
        e1 = E(w, A, 'oveq12d', [ab[k1], ser[k2]], '( ( abs ` %s ) x. %s )' % (SQ(k1), SQ(k2)), '( %s x. %s )' % (PR('( abs ` %s )' % V(k1)), PR(V(k2)))) if False else None
        e1 = w.s([ab[k1], w.s([ser[k2]], 'eqcomd', '( %s -> %s = %s )' % (A, SQ(k2), PR(V(k2))))], 'oveq12d',
                 '( %s -> ( ( abs ` %s ) x. %s ) = ( %s x. %s ) )' % (A, SQ(k1), SQ(k2), PR('( abs ` %s )' % V(k1)), PR(V(k2))))
        pm = w.s([fin, D(w, A2, 'recnd', [a1c], '( abs ` %s ) e. CC' % V(k1)), D(w, A2, 'rpcnd', [f2[k2]], '%s e. CC' % V(k2))], 'fprodmul',
                 '( %s -> %s = ( %s x. %s ) )' % (A, PR('( ( abs ` %s ) x. %s )' % (V(k1), V(k2))), PR('( abs ` %s )' % V(k1)), PR(V(k2))))
        tr = D(w, A2, 'remulcld', [a1c, D(w, A2, 'rpred', [f2[k2]], '%s e. RR' % V(k2))], '( ( abs ` %s ) x. %s ) e. RR' % (V(k1), V(k2)))
        t0 = D(w, A2, 'mulge0d', [a1c, D(w, A2, 'rpred', [f2[k2]], '%s e. RR' % V(k2)), D(w, A2, 'absge0d', [f2[k1]], '0 <_ ( abs ` %s )' % V(k1)),
                                  D(w, A2, 'rpge0d', [f2[k2]], '0 <_ %s' % V(k2))], '0 <_ ( ( abs ` %s ) x. %s )' % (V(k1), V(k2)))
        return w.s([e1, pm], 'eqtr4d', '( %s -> ( ( abs ` %s ) x. %s ) = %s )' % (A, SQ(k1), SQ(k2), PR('( ( abs ` %s ) x. %s )' % (V(k1), V(k2))))), tr, t0

    lh, ltr, lt0 = side('Z', 'RV')
    rh, rtr, rt0 = side('V', 'RZ')
    hk = w.s([w.s([D(w, A2, 'simpl', [], A), w.inst('simpl')], 'syl', '( %s -> %s )' % (A2, L.HZV)), kn2], 'jca', '( %s -> ( %s /\\ k e. NN ) )' % (A2, L.HZV))
    tle = w.s([hk, w.inst('zl3eutc')], 'syl', '( %s -> ( ( abs ` %s ) x. %s ) <_ ( ( abs ` %s ) x. %s ) )' % (A2, V('Z'), V('RV'), V('V'), V('RZ')))
    ple = w.s([w.s([], 'nfv', 'F/ k %s' % A), fin, ltr, lt0, rtr, tle], 'fprodle',
              '( %s -> %s <_ %s )' % (A, PR('( ( abs ` %s ) x. %s )' % (V('Z'), V('RV'))), PR('( ( abs ` %s ) x. %s )' % (V('V'), V('RZ')))))
    w.qed([w.s([lh, ple], 'eqbrtrd', '( %s -> ( ( abs ` %s ) x. %s ) <_ %s )' % (A, SQ('Z'), SQ('RV'), PR('( ( abs ` %s ) x. %s )' % (V('V'), V('RZ'))))), rh],
          'breqtrrd', L.STATEMENTS['zl3gseq'])
    go(w)


def mapval(w, Ak, MAP, n_body, k_body, kmem, dom='NN'):
    """( Ak -> ( MAP ` k ) = k_body ), MAP = ( n e. dom |-> n_body ), kmem: ( Ak -> k e. dom )"""
    import congr as _C
    idx = w.s([], 'id', '( n = k -> n = k )')
    eqn, val = w.congr(n_body, {'n': 'k'}, 'n = k', {'n': idx})
    assert val == k_body, (val, k_body)
    fv = w.s([eqn, w.s([], 'eqid', '%s = %s' % (MAP, MAP))], 'fvmptg', '( ( k e. %s /\\ %s e. _V ) -> ( %s ` k ) = %s )' % (dom, k_body, MAP, k_body))
    ex = w.s([w.s([], 'fvex' if k_body.startswith('( abs `') or k_body.startswith('( seq') else 'ovex', '%s e. _V' % k_body)], 'a1i', '( %s -> %s e. _V )' % (Ak, k_body))
    return w.s([kmem, ex, fv], 'syl2anc', '( %s -> ( %s ` k ) = %s )' % (Ak, MAP, k_body))


# ---------------------------------------------------------------- zl3gmono
if __name__ == '__main__' and want('zl3gmono'):
    w = W('zl3gmono', 'The gamma function at two points with the same absolute imaginary part and real parts ` 0 < Re Z <_ Re V ` : '
          '` | Gamma ( Z ) | / Gamma ( Re Z ) <_ | Gamma ( V ) | / Gamma ( Re V ) ` .  The limit of ~ zl3gseq through ~ gamcvg2 , '
          'with the factor ` Z ` of the limit compared by ~ zl3rab .')
    A = L.HZV
    Z0 = '( ZZ>= ` 1 )'
    Ak = '( %s /\\ k e. %s )' % (A, Z0)
    zc = D(w, A, 'simpll', [], 'Z e. CC'); vc = D(w, A, 'simplr', [], 'V e. CC')
    hh = D(w, A, 'simpr', [], '( ( abs ` ( Im ` Z ) ) = ( abs ` ( Im ` V ) ) /\\ 0 < ( Re ` Z ) /\\ ( Re ` Z ) <_ ( Re ` V ) )')
    z0 = D(w, A, 'simp2d', [hh], '0 < ( Re ` Z )')
    zv = D(w, A, 'simp3d', [hh], '( Re ` Z ) <_ ( Re ` V )')
    zr = D(w, A, 'recld', [zc], '( Re ` Z ) e. RR'); vr = D(w, A, 'recld', [vc], '( Re ` V ) e. RR')
    v0 = D(w, A, 'ltletrd', [a1(w, A, '0re', '0 e. RR'), zr, vr, z0, zv], '0 < ( Re ` V )')
    zp = w.s([zc, z0], 'jca', '( %s -> ( Z e. CC /\\ 0 < ( Re ` Z ) ) )' % A)
    vp = w.s([vc, v0], 'jca', '( %s -> ( V e. CC /\\ 0 < ( Re ` V ) ) )' % A)
    X = {'Z': 'Z', 'V': 'V', 'RV': '( Re ` V )', 'RZ': '( Re ` Z )'}
    T = {k: L.EUT(v) for k, v in X.items()}
    mem = {}
    mem['Z'] = w.s([zp, w.inst('zrenn')], 'syl', '( %s -> Z e. ( CC \\ ( ZZ \\ NN ) ) )' % A)
    mem['V'] = w.s([vp, w.inst('zrenn')], 'syl', '( %s -> V e. ( CC \\ ( ZZ \\ NN ) ) )' % A)
    for key, r, p0 in (('RV', vr, v0), ('RZ', zr, z0)):
        x = X[key]
        rr = w.s([r, w.inst('rered')], 'syl', '( %s -> ( Re ` %s ) = %s )' % (A, x, x))
        pos = w.s([p0, rr], 'breqtrrd', '( %s -> 0 < ( Re ` %s ) )' % (A, x))
        xp = w.s([D(w, A, 'recnd', [r], '%s e. CC' % x), pos], 'jca', '( %s -> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (A, x, x))
        mem[key] = w.s([xp, w.inst('zrenn')], 'syl', '( %s -> %s e. ( CC \\ ( ZZ \\ NN ) ) )' % (A, x))
    lim = {}
    for key in X:
        lim[key] = w.s([w.s([], 'eqid', '%s = %s' % (T[key], T[key])), mem[key]], 'gamcvg2',
                       '( %s -> seq 1 ( x. , %s ) ~~> ( ( _G ` %s ) x. %s ) )' % (A, T[key], X[key], X[key]))
    # context k e. ( ZZ>= ` 1 )
    kz = D(w, Ak, 'simpr', [], 'k e. %s' % Z0)
    kn = w.s([kz, w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'a1i', '( %s -> NN = ( ZZ>= ` 1 ) )' % Ak)], 'eleqtrrd', '( %s -> k e. NN )' % Ak)
    Aka = '( %s /\\ a e. ( 1 ... k ) )' % Ak
    an = w.s([D(w, Aka, 'simpr', [], 'a e. ( 1 ... k )'), w.inst('elfznn')], 'syl', '( %s -> a e. NN )' % Aka)
    SQ = lambda key, n: '( seq 1 ( x. , %s ) ` %s )' % (T[key], n)
    sc = {}
    for key, pre in (('Z', zp), ('V', vp)):
        pa = w.s([w.s([pre], 'adantr', '( %s -> %s )' % (Ak, formula_rhs(w, pre))) if False else D(w, Ak, 'adantr', [pre], '( %s e. CC /\\ 0 < ( Re ` %s ) )' % (X[key], X[key])), ], 'idi', 'x') if False else None
        pk = D(w, Ak, 'adantr', [pre], '( %s e. CC /\\ 0 < ( Re ` %s ) )' % (X[key], X[key]))
        pka = w.s([D(w, Aka, 'adantr', [pk], '( %s e. CC /\\ 0 < ( Re ` %s ) )' % (X[key], X[key])), an], 'jca',
                  '( %s -> ( ( %s e. CC /\\ 0 < ( Re ` %s ) ) /\\ a e. NN ) )' % (Aka, X[key], X[key]))
        t = w.s([pka, w.inst('eutzcl')], 'syl', '( %s -> ( %s ` a ) e. CC )' % (Aka, T[key]))
        clo = D(w, '( %s /\\ ( a e. CC /\\ b e. CC ) )' % Ak, 'mulcld', [D(w, '( %s /\\ ( a e. CC /\\ b e. CC ) )' % Ak, 'simprl', [], 'a e. CC'),
                                                                  D(w, '( %s /\\ ( a e. CC /\\ b e. CC ) )' % Ak, 'simprr', [], 'b e. CC')], '( a x. b ) e. CC')
        sc[key] = w.s([kz, t, clo], 'seqcl', '( %s -> %s e. CC )' % (Ak, SQ(key, 'k')))
    for key, base, pre in (('RV', 'V', vp), ('RZ', 'Z', zp)):
        pk = D(w, Ak, 'adantr', [pre], '( %s e. CC /\\ 0 < ( Re ` %s ) )' % (base, base))
        pka = w.s([D(w, Aka, 'adantr', [pk], '( %s e. CC /\\ 0 < ( Re ` %s ) )' % (base, base)), an], 'jca',
                  '( %s -> ( ( %s e. CC /\\ 0 < ( Re ` %s ) ) /\\ a e. NN ) )' % (Aka, base, base))
        t = D(w, Aka, 'rpred', [w.s([pka, w.inst('eutxrp')], 'syl', '( %s -> ( %s ` a ) e. RR+ )' % (Aka, T[key]))], '( %s ` a ) e. RR' % T[key])
        AR = '( %s /\\ ( a e. RR /\\ b e. RR ) )' % Ak
        clo = D(w, AR, 'remulcld', [D(w, AR, 'simprl', [], 'a e. RR'), D(w, AR, 'simprr', [], 'b e. RR')], '( a x. b ) e. RR')
        sc[key] = w.s([kz, t, clo], 'seqcl', '( %s -> %s e. RR )' % (Ak, SQ(key, 'k')))
    one = a1(w, A, '1z', '1 e. ZZ')
    zeq = w.s([], 'eqid', '%s = %s' % (Z0, Z0))
    res = {}
    for k1, k2 in (('Z', 'RV'), ('V', 'RZ')):
        HA = '( n e. NN |-> ( abs ` %s ) )' % SQ(k1, 'n')
        HL = '( n e. NN |-> ( ( abs ` %s ) x. %s ) )' % (SQ(k1, 'n'), SQ(k2, 'n'))
        exA = w.s([w.s([w.s([], 'nnex', 'NN e. _V'), w.inst('mptexg')], 'ax-mp', '%s e. _V' % HA)], 'a1i', '( %s -> %s e. _V )' % (A, HA))
        exL = w.s([w.s([w.s([], 'nnex', 'NN e. _V'), w.inst('mptexg')], 'ax-mp', '%s e. _V' % HL)], 'a1i', '( %s -> %s e. _V )' % (A, HL))
        vA = mapval(w, Ak, HA, '( abs ` %s )' % SQ(k1, 'n'), '( abs ` %s )' % SQ(k1, 'k'), kn)
        vL = mapval(w, Ak, HL, '( ( abs ` %s ) x. %s )' % (SQ(k1, 'n'), SQ(k2, 'n')), '( ( abs ` %s ) x. %s )' % (SQ(k1, 'k'), SQ(k2, 'k')), kn)
        G1 = '( ( _G ` %s ) x. %s )' % (X[k1], X[k1]); G2 = '( ( _G ` %s ) x. %s )' % (X[k2], X[k2])
        la = w.s([zeq, lim[k1], exA, one, sc[k1], vA], 'climabs', '( %s -> %s ~~> ( abs ` %s ) )' % (A, HA, G1))
        vAc = w.s([vA, D(w, Ak, 'recnd', [D(w, Ak, 'abscld', [sc[k1]], '( abs ` %s ) e. RR' % SQ(k1, 'k'))], '( abs ` %s ) e. CC' % SQ(k1, 'k'))],
                  'eqeltrd', '( %s -> ( %s ` k ) e. CC )' % (Ak, HA))
        vLm = w.s([vL, w.s([vA], 'oveq1d', '( %s -> ( ( %s ` k ) x. %s ) = ( ( abs ` %s ) x. %s ) )' % (Ak, HA, SQ(k2, 'k'), SQ(k1, 'k'), SQ(k2, 'k')))],
                  'eqtr4d', '( %s -> ( %s ` k ) = ( ( %s ` k ) x. %s ) )' % (Ak, HL, HA, SQ(k2, 'k')))
        ll = w.s([zeq, one, la, exL, lim[k2], vAc, D(w, Ak, 'recnd', [sc[k2]], '%s e. CC' % SQ(k2, 'k')), vLm], 'climmul',
                 '( %s -> %s ~~> ( ( abs ` %s ) x. %s ) )' % (A, HL, G1, G2))
        vLr = w.s([vL, D(w, Ak, 'remulcld', [D(w, Ak, 'abscld', [sc[k1]], '( abs ` %s ) e. RR' % SQ(k1, 'k')), sc[k2]], '( ( abs ` %s ) x. %s ) e. RR' % (SQ(k1, 'k'), SQ(k2, 'k')))],
                  'eqeltrd', '( %s -> ( %s ` k ) e. RR )' % (Ak, HL))
        res[k1] = (HL, ll, vL, vLr, G1, G2)
    HL, ll, vL, vLr, G1, G2 = res['Z']
    HR, rl, vR, vRr, G3, G4 = res['V']
    gs = w.s([w.s([D(w, Ak, 'simpl', [], A), kn], 'jca', '( %s -> ( %s /\\ k e. NN ) )' % (Ak, A)), w.inst('zl3gseq')], 'syl',
             '( %s -> ( ( abs ` %s ) x. %s ) <_ ( ( abs ` %s ) x. %s ) )' % (Ak, SQ('Z', 'k'), SQ('RV', 'k'), SQ('V', 'k'), SQ('RZ', 'k')))
    kle = w.s([w.s([vL, gs], 'eqbrtrd', '( %s -> ( %s ` k ) <_ ( ( abs ` %s ) x. %s ) )' % (Ak, HL, SQ('V', 'k'), SQ('RZ', 'k'))), vR], 'breqtrrd',
              '( %s -> ( %s ` k ) <_ ( %s ` k ) )' % (Ak, HL, HR))
    lim_le = w.s([zeq, one, ll, rl, vLr, vRr, kle], 'climle', '( %s -> ( ( abs ` %s ) x. %s ) <_ ( ( abs ` %s ) x. %s ) )' % (A, G1, G2, G3, G4))
    # algebra
    gZ = D(w, A, 'gamcld' if False else 'syl', [], 'x') if False else None
    gzc = w.s([mem['Z'], w.inst('gamcl')], 'syl', '( %s -> ( _G ` Z ) e. CC )' % A)
    gvc = w.s([mem['V'], w.inst('gamcl')], 'syl', '( %s -> ( _G ` V ) e. CC )' % A)
    grv = w.s([w.s([vr, v0], 'jca', '( %s -> ( ( Re ` V ) e. RR /\\ 0 < ( Re ` V ) ) )' % A), w.inst('gamrrp')], 'syl', '( %s -> ( _G ` ( Re ` V ) ) e. RR+ )' % A)
    grz = w.s([w.s([zr, z0], 'jca', '( %s -> ( ( Re ` Z ) e. RR /\\ 0 < ( Re ` Z ) ) )' % A), w.inst('gamrrp')], 'syl', '( %s -> ( _G ` ( Re ` Z ) ) e. RR+ )' % A)
    g1, g2, g3, g4 = '( abs ` ( _G ` Z ) )', '( _G ` ( Re ` V ) )', '( abs ` ( _G ` V ) )', '( _G ` ( Re ` Z ) )'
    x, y, a, b = '( Re ` Z )', '( Re ` V )', '( abs ` Z )', '( abs ` V )'
    cc = lambda t, st: D(w, A, 'recnd', [st], '%s e. CC' % t)
    g1r = D(w, A, 'abscld', [gzc], '%s e. RR' % g1); g3r = D(w, A, 'abscld', [gvc], '%s e. RR' % g3)
    g2r = D(w, A, 'rpred', [grv], '%s e. RR' % g2); g4r = D(w, A, 'rpred', [grz], '%s e. RR' % g4)
    ar = D(w, A, 'abscld', [zc], '%s e. RR' % a); br = D(w, A, 'abscld', [vc], '%s e. RR' % b)
    e1 = E(w, A, 'absmuld', [gzc, zc], '( abs ` %s )' % G1, '( %s x. %s )' % (g1, a))
    e2 = E(w, A, 'absmuld', [gvc, vc], '( abs ` %s )' % G3, '( %s x. %s )' % (g3, b))
    L0 = '( ( %s x. %s ) x. ( %s x. %s ) )' % (g1, a, g2, y)
    R0 = '( ( %s x. %s ) x. ( %s x. %s ) )' % (g3, b, g4, x)
    l1 = E(w, A, 'oveq1d', [e1], '( ( abs ` %s ) x. %s )' % (G1, G2), '( ( %s x. %s ) x. %s )' % (g1, a, G2))
    r1 = E(w, A, 'oveq1d', [e2], '( ( abs ` %s ) x. %s )' % (G3, G4), '( ( %s x. %s ) x. %s )' % (g3, b, G4))
    ineq = w.s([w.s([l1, lim_le], 'eqbrtrrd', '( %s -> ( ( %s x. %s ) x. %s ) <_ ( ( abs ` %s ) x. %s ) )' % (A, g1, a, G2, G3, G4)), r1], 'breqtrd',
               '( %s -> ( ( %s x. %s ) x. %s ) <_ ( ( %s x. %s ) x. %s ) )' % (A, g1, a, G2, g3, b, G4))
    m1 = E(w, A, 'mul4d', [cc(g1, g1r), cc(a, ar), cc(g2, g2r), D(w, A, 'recnd', [vr], '%s e. CC' % y)],
           '( ( %s x. %s ) x. %s )' % (g1, a, G2), '( ( %s x. %s ) x. ( %s x. %s ) )' % (g1, g2, a, y))
    m2 = E(w, A, 'mul4d', [cc(g3, g3r), cc(b, br), cc(g4, g4r), D(w, A, 'recnd', [zr], '%s e. CC' % x)],
           '( ( %s x. %s ) x. %s )' % (g3, b, G4), '( ( %s x. %s ) x. ( %s x. %s ) )' % (g3, g4, b, x))
    P12, P34 = '( %s x. %s )' % (g1, g2), '( %s x. %s )' % (g3, g4)
    in2 = w.s([w.s([m1, ineq], 'eqbrtrrd', '( %s -> ( %s x. ( %s x. %s ) ) <_ ( ( %s x. %s ) x. %s ) )' % (A, P12, a, y, g3, b, G4)), m2], 'breqtrd',
              '( %s -> ( %s x. ( %s x. %s ) ) <_ ( %s x. ( %s x. %s ) ) )' % (A, P12, a, y, P34, b, x))
    rab = w.s([w.s([w.s([zc, vc], 'jca', '( %s -> ( Z e. CC /\\ V e. CC ) )' % A), hh], 'jca', '( %s -> %s )' % (A, A)) if False else w.s([], 'id', '( %s -> %s )' % (A, A)), w.inst('zl3rab')],
              'syl', '( %s -> ( %s x. %s ) <_ ( %s x. %s ) )' % (A, x, b, y, a))
    c1 = E(w, A, 'mulcomd', [D(w, A, 'recnd', [br], '%s e. CC' % b), D(w, A, 'recnd', [zr], '%s e. CC' % x)], '( %s x. %s )' % (b, x), '( %s x. %s )' % (x, b))
    c2 = E(w, A, 'mulcomd', [D(w, A, 'recnd', [ar], '%s e. CC' % a), D(w, A, 'recnd', [vr], '%s e. CC' % y)], '( %s x. %s )' % (a, y), '( %s x. %s )' % (y, a))
    rab2 = w.s([w.s([c1, rab], 'eqbrtrd', '( %s -> ( %s x. %s ) <_ ( %s x. %s ) )' % (A, b, x, y, a)), c2], 'breqtrrd', '( %s -> ( %s x. %s ) <_ ( %s x. %s ) )' % (A, b, x, a, y))
    p34r = D(w, A, 'remulcld', [g3r, g4r], '%s e. RR' % P34)
    p340 = D(w, A, 'mulge0d', [g3r, g4r, D(w, A, 'absge0d', [gvc], '0 <_ %s' % g3), D(w, A, 'rpge0d', [grz], '0 <_ %s' % g4)], '0 <_ %s' % P34)
    in3 = D(w, A, 'lemul2ad', [D(w, A, 'remulcld', [br, zr], '( %s x. %s ) e. RR' % (b, x)), D(w, A, 'remulcld', [ar, vr], '( %s x. %s ) e. RR' % (a, y)), p34r, p340, rab2],
            '( %s x. ( %s x. %s ) ) <_ ( %s x. ( %s x. %s ) )' % (P34, b, x, P34, a, y))
    in4 = D(w, A, 'letrd', [D(w, A, 'remulcld', [D(w, A, 'remulcld', [g1r, g2r], '%s e. RR' % P12), D(w, A, 'remulcld', [ar, vr], '( %s x. %s ) e. RR' % (a, y))], '( %s x. ( %s x. %s ) ) e. RR' % (P12, a, y)),
                            D(w, A, 'remulcld', [p34r, D(w, A, 'remulcld', [br, zr], '( %s x. %s ) e. RR' % (b, x))], '( %s x. ( %s x. %s ) ) e. RR' % (P34, b, x)),
                            D(w, A, 'remulcld', [p34r, D(w, A, 'remulcld', [ar, vr], '( %s x. %s ) e. RR' % (a, y))], '( %s x. ( %s x. %s ) ) e. RR' % (P34, a, y)), in2, in3],
            '( %s x. ( %s x. %s ) ) <_ ( %s x. ( %s x. %s ) )' % (P12, a, y, P34, a, y))
    # a y > 0: a >= Re Z > 0
    apos = D(w, A, 'ltletrd', [a1(w, A, '0re', '0 e. RR'), zr, ar, z0, w.s([zc, w.inst('releabs')], 'syl', '( %s -> %s <_ %s )' % (A, x, a))], '0 < %s' % a)
    ay = D(w, A, 'rpmulcld', [D(w, A, 'elrpd', [ar, apos], '%s e. RR+' % a), D(w, A, 'elrpd', [vr, v0], '%s e. RR+' % y)], '( %s x. %s ) e. RR+' % (a, y))
    bi = D(w, A, 'lemul1d', [D(w, A, 'remulcld', [g1r, g2r], '%s e. RR' % P12), p34r, ay], '( %s <_ %s <-> ( %s x. ( %s x. %s ) ) <_ ( %s x. ( %s x. %s ) ) )' % (P12, P34, P12, a, y, P34, a, y))
    w.qed([in4, bi], 'mpbird', L.STATEMENTS['zl3gmono'])
    go(w)


# ---------------------------------------------------------------- zl3grat
if __name__ == '__main__' and want('zl3grat'):
    w = W('zl3grat', 'The gamma function on ` [ 1 / 100 , 3 ] ` is bounded above and below by positive constants, so the ratio of two of '
          'its values is bounded: ~ lgambdd at ` R = 100 ` as in ~ gamrbd , whose steps this proof extends by the lower bound.')
    src = open('worksheets/gamrbd.mmp').read().split('\n')
    body = []
    for l in src:
        if l.startswith('s296:'):
            break
        if l[:1] in ('s', 'i') and ':' in l:
            head, rest = l.split(':', 1)
            hyps, rest2 = rest.split(':', 1)
            hyps = ','.join('g' + h for h in hyps.split(',') if h)
            body.append('g%s:%s:%s' % (head, hyps, rest2))
    w.lines.extend(body)
    U = "{ a e. CC | ( ( abs ` a ) <_ ; ; 1 0 0 /\\ A. b e. NN0 ( 1 / ; ; 1 0 0 ) <_ ( abs ` ( a + b ) ) ) }"
    PH = '( ; ; 1 0 0 e. NN /\\ ( r e. RR /\\ A. c e. %s ( abs ` ( log_G ` c ) ) <_ r ) )' % U
    I = '( ( 1 / ; ; 1 0 0 ) [,] 3 )'
    Ap = '( %s /\\ p e. %s )' % (PH, I)
    LG = '( log_G ` p )'
    # lower bound in context Ap from the gamrbd steps s251 ( |log_G p| <_ r ), s274 (log_G p e. CC), s281, s279
    rlg = D(w, Ap, 'recld', ['gs274'], '( Re ` %s ) e. RR' % LG)
    rr = D(w, Ap, 'adantr', ['gs7'], 'r e. RR')
    arle = w.s(['gs274', w.inst('absrele')], 'syl', '( %s -> ( abs ` ( Re ` %s ) ) <_ ( abs ` %s ) )' % (Ap, LG, LG))
    arr = D(w, Ap, 'letrd', [D(w, Ap, 'abscld', [D(w, Ap, 'recnd', [rlg], '( Re ` %s ) e. CC' % LG)], '( abs ` ( Re ` %s ) ) e. RR' % LG), 'gs285', rr, arle, 'gs251'], '( abs ` ( Re ` %s ) ) <_ r' % LG)
    lo = D(w, Ap, 'simpld', [w.s([arr, D(w, Ap, 'absled', [rlg, rr], '( ( abs ` ( Re ` %s ) ) <_ r <-> ( -u r <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ r ) )' % (LG, LG, LG))],
                                 'mpbid', '( %s -> ( -u r <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ r ) )' % (Ap, LG, LG))], '-u r <_ ( Re ` %s )' % LG)
    nr = D(w, Ap, 'renegcld', [rr], '-u r e. RR')
    elo = efle_(w, Ap, '-u r', '( Re ` %s )' % LG, nr, rlg, lo)
    elo2 = w.s([elo, w.s(['gs281', 'gs279'], 'eqtr3d', '( %s -> ( exp ` ( Re ` %s ) ) = ( _G ` p ) )' % (Ap, LG)) if False else
                w.s([w.s(['gs281'], 'eqcomd', '( %s -> ( exp ` ( Re ` %s ) ) = ( abs ` ( _G ` p ) ) )' % (Ap, LG)), 'gs279'], 'eqtrd',
                    '( %s -> ( exp ` ( Re ` %s ) ) = ( _G ` p ) )' % (Ap, LG))], 'breqtrd', '( %s -> ( exp ` -u r ) <_ ( _G ` p ) )' % Ap)
    BOTH = lambda v: '( ( _G ` %s ) <_ ( exp ` r ) /\\ ( exp ` -u r ) <_ ( _G ` %s ) )' % (v, v)
    both = w.s(['gs295', elo2], 'jca', '( %s -> %s )' % (Ap, BOTH('p')))
    allp = w.s([both], 'ralrimiva', '( %s -> A. p e. %s %s )' % (PH, I, BOTH('p')))
    Apq = '( %s /\\ ( p e. %s /\\ q e. %s ) )' % (PH, I, I)
    allpq = D(w, Apq, 'adantr', [allp], 'A. p e. %s %s' % (I, BOTH('p')))
    pin = D(w, Apq, 'simprl', [], 'p e. %s' % I); qin = D(w, Apq, 'simprr', [], 'q e. %s' % I)
    idp = w.s([], 'biid', '( %s <-> %s )' % (BOTH('p'), BOTH('p')))
    # instantiate at q: ( p = q -> ( BOTH p <-> BOTH q ) )
    idx = w.s([], 'id', '( p = q -> p = q )')
    stq, valq = w.wcongr(BOTH('p'), {'p': 'q'}, 'p = q', {'p': idx})
    atq = w.s([stq, allpq, qin], 'rspcdva', '( %s -> %s )' % (Apq, BOTH('q')))
    idx2 = w.s([], 'id', '( p = p -> p = p )') if False else None
    atp = w.s([allpq, pin, w.inst('rspa') if False else w.s([], 'rsp', '( A. p e. %s %s -> ( p e. %s -> %s ) )' % (I, BOTH('p'), I, BOTH('p')))], 'sylc' if False else 'syl2anc', 'x') if False else None
    atp = w.s([w.s([allpq, w.s([], 'rsp', '( A. p e. %s %s -> ( p e. %s -> %s ) )' % (I, BOTH('p'), I, BOTH('p')))], 'syl', '( %s -> ( p e. %s -> %s ) )' % (Apq, I, BOTH('p'))), pin],
              'mpid' if False else 'mpd', '( %s -> %s )' % (Apq, BOTH('p'))) if False else None
    rs = w.s([allpq, w.s([], 'rsp', '( A. p e. %s %s -> ( p e. %s -> %s ) )' % (I, BOTH('p'), I, BOTH('p')))], 'syl', '( %s -> ( p e. %s -> %s ) )' % (Apq, I, BOTH('p')))
    atp = w.s([pin, rs], 'mpd', '( %s -> %s )' % (Apq, BOTH('p')))
    gp = D(w, Apq, 'simpld', [atp], '( _G ` p ) <_ ( exp ` r )')
    gq = D(w, Apq, 'simprd', [atq], '( exp ` -u r ) <_ ( _G ` q )')
    rrq = D(w, Apq, 'adantr', ['gs7'], 'r e. RR')
    er = D(w, Apq, 'rpefcld' if False else 'syl', [], 'x') if False else w.s([rrq, w.inst('rpefcl')], 'syl', '( %s -> ( exp ` r ) e. RR+ )' % Apq)
    enr = w.s([D(w, Apq, 'renegcld', [rrq], '-u r e. RR'), w.inst('rpefcl')], 'syl', '( %s -> ( exp ` -u r ) e. RR+ )' % Apq)
    DD = '( ( exp ` r ) / ( exp ` -u r ) )'
    ddp = D(w, Apq, 'rpdivcld', [er, enr], '%s e. RR+' % DD)
    gqr = D(w, Apq, 'rpred', [w.s([w.s([D(w, Apq, 'syl', [qin, w.inst('elicc2')], 'x') if False else None], 'idi', 'x') if False else None], 'idi', 'x') if False else
                              None], 'x') if False else None
    # Gamma ( q ) e. RR: from the interval
    one100 = w.s([], 'idi', 'x') if False else None
    qr_ = w.s([qin, w.s([w.s(['gs22', w.s([], '3re', '3 e. RR')], 'iccssre', '( ( 1 / ; ; 1 0 0 ) [,] 3 ) C_ RR')], 'sseli' if False else 'idi', '( ( 1 / ; ; 1 0 0 ) [,] 3 ) C_ RR')], 'sseldi' if False else 'sseldd' if False else 'syl', 'x') if False else None
    icc = w.s(['gs22', w.s([], '3re', '3 e. RR'), w.inst('iccssre')], 'mp2an', '( ( 1 / ; ; 1 0 0 ) [,] 3 ) C_ RR')
    qre = w.s([w.s([icc], 'a1i', '( %s -> ( ( 1 / ; ; 1 0 0 ) [,] 3 ) C_ RR )' % Apq), qin], 'sseldd', '( %s -> q e. RR )' % Apq)
    q0 = D(w, Apq, 'ltletrd', [a1(w, Apq, '0re', '0 e. RR'), w.s(['gs22'], 'a1i', '( %s -> ( 1 / ; ; 1 0 0 ) e. RR )' % Apq), qre,
                               w.s([w.s(['gs21'], 'rpgt0i' if False else 'idi', '( 1 / ; ; 1 0 0 ) e. RR+')], 'a1i', 'x') if False else
                               w.s([w.s([w.s(['gs21', w.inst('rpgt0')], 'ax-mp', '0 < ( 1 / ; ; 1 0 0 )')], 'a1i', '( %s -> 0 < ( 1 / ; ; 1 0 0 ) )' % Apq)], 'idi', '( %s -> 0 < ( 1 / ; ; 1 0 0 ) )' % Apq),
                               D(w, Apq, 'simp2d', [w.s([qin, w.s([w.s(['gs22', w.s([], '3re', '3 e. RR')], 'elicc2i' if False else 'elicc2', 'x')], 'idi', 'x') if False else
                                                          w.s([w.s(['gs22'], 'a1i', '( %s -> ( 1 / ; ; 1 0 0 ) e. RR )' % Apq), a1(w, Apq, '3re', '3 e. RR'), w.inst('elicc2')], 'syl2anc',
                                                              '( %s -> ( q e. ( ( 1 / ; ; 1 0 0 ) [,] 3 ) <-> ( q e. RR /\\ ( 1 / ; ; 1 0 0 ) <_ q /\\ q <_ 3 ) ) )' % Apq)],
                                                         'mpbid', '( %s -> ( q e. RR /\\ ( 1 / ; ; 1 0 0 ) <_ q /\\ q <_ 3 ) )' % Apq)], '( 1 / ; ; 1 0 0 ) <_ q')],
            '0 < q')
    gqrp = w.s([w.s([qre, q0], 'jca', '( %s -> ( q e. RR /\\ 0 < q ) )' % Apq), w.inst('gamrrp')], 'syl', '( %s -> ( _G ` q ) e. RR+ )' % Apq)
    m = D(w, Apq, 'lemul2ad', [D(w, Apq, 'rpred', [enr], '( exp ` -u r ) e. RR'), D(w, Apq, 'rpred', [gqrp], '( _G ` q ) e. RR'), D(w, Apq, 'rpred', [ddp], '%s e. RR' % DD),
                               D(w, Apq, 'rpge0d', [ddp], '0 <_ %s' % DD), gq], '( %s x. ( exp ` -u r ) ) <_ ( %s x. ( _G ` q ) )' % (DD, DD))
    dc = E(w, Apq, 'divcan1d', [D(w, Apq, 'rpcnd', [er], '( exp ` r ) e. CC'), D(w, Apq, 'rpcnd', [enr], '( exp ` -u r ) e. CC'), D(w, Apq, 'rpne0d', [enr], '( exp ` -u r ) =/= 0')],
           '( %s x. ( exp ` -u r ) )' % DD, '( exp ` r )')
    m2 = w.s([dc, m], 'eqbrtrrd', '( %s -> ( exp ` r ) <_ ( %s x. ( _G ` q ) ) )' % (Apq, DD))
    fin = D(w, Apq, 'letrd', [D(w, Apq, 'rpred', [atp and w.s([gp], 'idi', '( %s -> ( _G ` p ) <_ ( exp ` r ) )' % Apq) and
                                                   w.s([w.s([w.s([D(w, Apq, 'simprl', [], 'p e. %s' % I), w.s([icc], 'a1i', '( %s -> ( ( 1 / ; ; 1 0 0 ) [,] 3 ) C_ RR )' % Apq)], 'idi', 'x')], 'idi', 'x')], 'idi', 'x') if False else None], 'x') if False else None,
                              ], 'x') if False else None
    pre = w.s([w.s([icc], 'a1i', '( %s -> ( ( 1 / ; ; 1 0 0 ) [,] 3 ) C_ RR )' % Apq), pin], 'sseldd', '( %s -> p e. RR )' % Apq)
    ppos = D(w, Apq, 'ltletrd', [a1(w, Apq, '0re', '0 e. RR'), w.s(['gs22'], 'a1i', '( %s -> ( 1 / ; ; 1 0 0 ) e. RR )' % Apq), pre,
                                 w.s([w.s(['gs21', w.inst('rpgt0')], 'ax-mp', '0 < ( 1 / ; ; 1 0 0 )')], 'a1i', '( %s -> 0 < ( 1 / ; ; 1 0 0 ) )' % Apq),
                                 D(w, Apq, 'simp2d', [w.s([pin, w.s([w.s(['gs22'], 'a1i', '( %s -> ( 1 / ; ; 1 0 0 ) e. RR )' % Apq), a1(w, Apq, '3re', '3 e. RR'), w.inst('elicc2')], 'syl2anc',
                                                                     '( %s -> ( p e. ( ( 1 / ; ; 1 0 0 ) [,] 3 ) <-> ( p e. RR /\\ ( 1 / ; ; 1 0 0 ) <_ p /\\ p <_ 3 ) ) )' % Apq)],
                                                          'mpbid', '( %s -> ( p e. RR /\\ ( 1 / ; ; 1 0 0 ) <_ p /\\ p <_ 3 ) )' % Apq)], '( 1 / ; ; 1 0 0 ) <_ p')], '0 < p')
    gprp = w.s([w.s([pre, ppos], 'jca', '( %s -> ( p e. RR /\\ 0 < p ) )' % Apq), w.inst('gamrrp')], 'syl', '( %s -> ( _G ` p ) e. RR+ )' % Apq)
    fin = D(w, Apq, 'letrd', [D(w, Apq, 'rpred', [gprp], '( _G ` p ) e. RR'), D(w, Apq, 'rpred', [er], '( exp ` r ) e. RR'),
                              D(w, Apq, 'remulcld', [D(w, Apq, 'rpred', [ddp], '%s e. RR' % DD), D(w, Apq, 'rpred', [gqrp], '( _G ` q ) e. RR')], '( %s x. ( _G ` q ) ) e. RR' % DD),
                              gp, m2], '( _G ` p ) <_ ( %s x. ( _G ` q ) )' % DD)
    allf = w.s([fin], 'ralrimivva', '( %s -> A. p e. %s A. q e. %s ( _G ` p ) <_ ( %s x. ( _G ` q ) ) )' % (PH, I, I, DD))
    # E. d
    idd = w.s([], 'id', '( d = %s -> d = %s )' % (DD, DD))
    std, vald = w.wcongr('A. p e. %s A. q e. %s ( _G ` p ) <_ ( d x. ( _G ` q ) )' % (I, I), {'d': DD}, 'd = %s' % DD, {'d': idd})
    stdd = w.s([std], 'adantl', '( ( %s /\\ d = %s ) -> ( A. p e. %s A. q e. %s ( _G ` p ) <_ ( d x. ( _G ` q ) ) <-> %s ) )' % (PH, DD, I, I, vald))
    er0 = w.s([w.s(['gs7', w.inst('rpefcl')], 'syl', '( %s -> ( exp ` r ) e. RR+ )' % PH),
               w.s([w.s(['gs7'], 'renegcld', '( %s -> -u r e. RR )' % PH), w.inst('rpefcl')], 'syl', '( %s -> ( exp ` -u r ) e. RR+ )' % PH)], 'rpdivcld', '( %s -> %s e. RR+ )' % (PH, DD))
    GOAL = L.STATEMENTS['zl3grat']
    ex = w.s([er0, stdd, allf], 'rspcedvd', '( %s -> %s )' % (PH, GOAL))
    lim = w.s([ex], 'rexlimdvaa', '( ; ; 1 0 0 e. NN -> ( E. r e. RR A. c e. %s ( abs ` ( log_G ` c ) ) <_ r -> %s ) )' % (U, GOAL))
    w.qed(['gs19', w.s(['gs4', lim], 'mpd', '( ; ; 1 0 0 e. NN -> %s )' % GOAL)], 'ax-mp', GOAL)
    go(w)


# ---------------------------------------------------------------- zl3igp1
if __name__ == '__main__' and want('zl3igp1'):
    from lin import lineq
    w = W('zl3igp1', 'The reciprocal gamma function right of ` Re = -1 ` as a quotient by ` Gamma ( U + 1 ) ` , valid at the pole ` U = 0 ` too '
          '( ~ igamval , ~ gamp1 ).')
    A, C = ante_of('zl3igp1')
    uc = D(w, A, 'simpl', [], 'U e. CC'); ur0 = D(w, A, 'simpr', [], '-u 1 < ( Re ` U )')
    c1 = a1(w, A, 'ax-1cn', '1 e. CC')
    U1 = '( U + 1 )'
    u1c = D(w, A, 'addcld', [uc, c1], '%s e. CC' % U1)
    re1 = w.s([E(w, A, 'readdd', [uc, c1], '( Re ` %s )' % U1, '( ( Re ` U ) + ( Re ` 1 ) )'),
               E(w, A, 'oveq2d', [w.s([w.s([], 're1', '( Re ` 1 ) = 1')], 'a1i', '( %s -> ( Re ` 1 ) = 1 )' % A)], '( ( Re ` U ) + ( Re ` 1 ) )', '( ( Re ` U ) + 1 )')],
              'eqtrd', '( %s -> ( Re ` %s ) = ( ( Re ` U ) + 1 ) )' % (A, U1))
    urr = D(w, A, 'recld', [uc], '( Re ` U ) e. RR')
    cl = Closure(w, A, {'( Re ` U )': ('RR', urr)})
    p1 = linarith(w, A, [ur0], '0 < ( ( Re ` U ) + 1 )', closure=cl)
    u1p = w.s([p1, re1], 'breqtrrd', '( %s -> 0 < ( Re ` %s ) )' % (A, U1))
    u1m = w.s([w.s([u1c, u1p], 'jca', '( %s -> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (A, U1, U1)), w.inst('zrenn')], 'syl', '( %s -> %s e. ( CC \\ ( ZZ \\ NN ) ) )' % (A, U1))
    g1c = w.s([u1m, w.inst('gamcl')], 'syl', '( %s -> ( _G ` %s ) e. CC )' % (A, U1))
    g1n = w.s([u1m, w.inst('gamne0')], 'syl', '( %s -> ( _G ` %s ) =/= 0 )' % (A, U1))
    ZN = '( ZZ \\ NN )'
    # case 1: U e. ( ZZ \ NN ) -> U = 0
    C1 = '( %s /\\ U e. %s )' % (A, ZN)
    um = D(w, C1, 'simpr', [], 'U e. %s' % ZN)
    uz = w.s([um, w.inst('eldifi')], 'syl', '( %s -> U e. ZZ )' % C1)
    unn = w.s([um, w.inst('eldifn')], 'syl', '( %s -> -. U e. NN )' % C1)
    C1b = '( %s /\\ 0 < U )' % C1
    unn2 = w.s([w.s([D(w, C1b, 'adantr', [uz], 'U e. ZZ'), D(w, C1b, 'simpr', [], '0 < U')], 'jca', '( %s -> ( U e. ZZ /\\ 0 < U ) )' % C1b),
                w.s([], 'elnnz', '( U e. NN <-> ( U e. ZZ /\\ 0 < U ) )')], 'sylibr', '( %s -> U e. NN )' % C1b)
    nlt = w.s([unn, unn2], 'mtand', '( %s -> -. 0 < U )' % C1)
    ur = D(w, C1, 'zred', [uz], 'U e. RR')
    z0 = a1(w, C1, '0re', '0 e. RR')
    ule = w.s([nlt, D(w, C1, 'lenltd', [ur, z0], '( U <_ 0 <-> -. 0 < U )')], 'mpbird', '( %s -> U <_ 0 )' % C1)
    rr = w.s([ur, w.inst('rered')], 'syl', '( %s -> ( Re ` U ) = U )' % C1)
    ltu = w.s([D(w, C1, 'adantr', [ur0], '-u 1 < ( Re ` U )'), rr], 'breqtrd', '( %s -> -u 1 < U )' % C1)
    zb = w.s([w.s([w.s([], 'neg1z', '-u 1 e. ZZ')], 'a1i', '( %s -> -u 1 e. ZZ )' % C1), uz, w.inst('zltp1le')], 'syl2anc', '( %s -> ( -u 1 < U <-> ( -u 1 + 1 ) <_ U ) )' % C1)
    ge = w.s([ltu, zb], 'mpbid', '( %s -> ( -u 1 + 1 ) <_ U )' % C1)
    cl1 = Closure(w, C1, {'U': ('RR', ur)})
    n1 = lineq(w, C1, '( -u 1 + 1 )', '0', closure=cl1)
    ge0 = w.s([n1, ge], 'eqbrtrrd', '( %s -> 0 <_ U )' % C1)
    u0 = w.s([w.s([ule, ge0], 'jca', '( %s -> ( U <_ 0 /\\ 0 <_ U ) )' % C1), D(w, C1, 'letri3d', [ur, z0], '( U = 0 <-> ( U <_ 0 /\\ 0 <_ U ) )')], 'mpbird', '( %s -> U = 0 )' % C1)
    l1 = w.s([um, w.inst('igamz')], 'syl', '( %s -> ( 1/_G ` U ) = 0 )' % C1)
    r1 = E(w, C1, 'oveq1d', [u0], '( U / ( _G ` %s ) )' % U1, '( 0 / ( _G ` %s ) )' % U1)
    r2 = w.s([D(w, C1, 'adantr', [g1c], '( _G ` %s ) e. CC' % U1), D(w, C1, 'adantr', [g1n], '( _G ` %s ) =/= 0' % U1), w.inst('div0')], 'syl2anc',
             '( %s -> ( 0 / ( _G ` %s ) ) = 0 )' % (C1, U1))
    case1 = w.s([l1, w.s([r1, r2], 'eqtrd', '( %s -> ( U / ( _G ` %s ) ) = 0 )' % (C1, U1))], 'eqtr4d', '( %s -> %s )' % (C1, C))
    # case 2
    C2 = '( %s /\\ -. U e. %s )' % (A, ZN)
    um2 = w.s([w.s([D(w, C2, 'adantr', [uc], 'U e. CC'), D(w, C2, 'simpr', [], '-. U e. %s' % ZN)], 'jca', '( %s -> ( U e. CC /\\ -. U e. %s ) )' % (C2, ZN)),
               w.s([], 'eldif', '( U e. ( CC \\ %s ) <-> ( U e. CC /\\ -. U e. %s ) )' % (ZN, ZN))], 'sylibr', '( %s -> U e. ( CC \\ %s ) )' % (C2, ZN))
    l2 = w.s([um2, w.inst('igamgam')], 'syl', '( %s -> ( 1/_G ` U ) = ( 1 / ( _G ` U ) ) )' % C2)
    gp = w.s([um2, w.inst('gamp1')], 'syl', '( %s -> ( _G ` %s ) = ( ( _G ` U ) x. U ) )' % (C2, U1))
    guc = w.s([um2, w.inst('gamcl')], 'syl', '( %s -> ( _G ` U ) e. CC )' % C2)
    gun = w.s([um2, w.inst('gamne0')], 'syl', '( %s -> ( _G ` U ) =/= 0 )' % C2)
    zin = w.s([w.s([w.s([], '0z', '0 e. ZZ'), w.s([], '0nnn', '-. 0 e. NN')], 'pm3.2i', '( 0 e. ZZ /\\ -. 0 e. NN )'),
               w.s([], 'eldif', '( 0 e. %s <-> ( 0 e. ZZ /\\ -. 0 e. NN ) )' % ZN)], 'mpbir', '0 e. %s' % ZN)
    une = w.s([w.s([w.s([zin], 'a1i', '( %s -> 0 e. %s )' % (C2, ZN)), D(w, C2, 'simpr', [], '-. U e. %s' % ZN)], 'jca', '( %s -> ( 0 e. %s /\\ -. U e. %s ) )' % (C2, ZN, ZN)),
               w.inst('nelne2')], 'syl', '( %s -> 0 =/= U )' % C2)
    une2 = D(w, C2, 'necomd', [une], 'U =/= 0')
    uc2 = D(w, C2, 'adantr', [uc], 'U e. CC')
    r1 = E(w, C2, 'oveq2d', [gp], '( U / ( _G ` %s ) )' % U1, '( U / ( ( _G ` U ) x. U ) )')
    r2 = E(w, C2, 'oveq1d', [w.s([E(w, C2, 'mullidd', [uc2], '( 1 x. U )', 'U')], 'eqcomd', '( %s -> U = ( 1 x. U ) )' % C2)], '( U / ( ( _G ` U ) x. U ) )', '( ( 1 x. U ) / ( ( _G ` U ) x. U ) )')
    r3 = E(w, C2, 'divcan5rd', [a1(w, C2, 'ax-1cn', '1 e. CC'), guc, uc2, gun, une2], '( ( 1 x. U ) / ( ( _G ` U ) x. U ) )', '( 1 / ( _G ` U ) )')
    rr2 = chain(w, C2, ['( U / ( _G ` %s ) )' % U1, '( U / ( ( _G ` U ) x. U ) )', '( ( 1 x. U ) / ( ( _G ` U ) x. U ) )', '( 1 / ( _G ` U ) )'], [r1, r2, r3])
    case2 = w.s([l2, rr2], 'eqtr4d', '( %s -> %s )' % (C2, C))
    w.qed([case1, case2], 'pm2.61dan', L.STATEMENTS['zl3igp1'])
    go(w)


# ---------------------------------------------------------------- zl3haff
if __name__ == '__main__' and want('zl3haff'):
    w = W('zl3haff', 'An affine map is holomorphic on every open set ( ~ z6ehdv , ~ zl2hent ).')
    A, C = ante_of('zl3haff')
    ac = D(w, A, 'simpll', [], 'A e. CC'); bc = D(w, A, 'simplr', [], 'B e. CC')
    op = D(w, A, 'simpr', [], 'D e. ( TopOpen ` CCfld )')
    S = w.s([w.s([], 'cnelprrecn', 'CC e. { RR , CC }')], 'a1i', '( %s -> CC e. { RR , CC } )' % A)
    As = '( %s /\\ s e. CC )' % A
    sc = D(w, As, 'simpr', [], 's e. CC')
    one = a1(w, As, 'ax-1cn', '1 e. CC')
    did = w.s([S], 'dvmptid', '( %s -> ( CC _D ( s e. CC |-> s ) ) = ( s e. CC |-> 1 ) )' % A)
    dmul = w.s([S, sc, one, did, ac], 'dvmptcmul', '( %s -> ( CC _D ( s e. CC |-> ( A x. s ) ) ) = ( s e. CC |-> ( A x. 1 ) ) )' % A)
    dc = w.s([S, bc], 'dvmptc', '( %s -> ( CC _D ( s e. CC |-> B ) ) = ( s e. CC |-> 0 ) )' % A)
    asc = D(w, As, 'mulcld', [D(w, As, 'adantr', [ac], 'A e. CC'), sc], '( A x. s ) e. CC')
    a1c = D(w, As, 'mulcld', [D(w, As, 'adantr', [ac], 'A e. CC'), one], '( A x. 1 ) e. CC')
    bsc = D(w, As, 'adantr', [bc], 'B e. CC')
    z0 = a1(w, As, '0cn', '0 e. CC')
    dadd = w.s([S, asc, a1c, dmul, bsc, z0, dc], 'dvmptadd', '( %s -> ( CC _D ( s e. CC |-> ( ( A x. s ) + B ) ) ) = ( s e. CC |-> ( ( A x. 1 ) + 0 ) ) )' % A)
    all1 = w.s([D(w, As, 'addcld', [asc, bsc], '( ( A x. s ) + B ) e. CC')], 'ralrimiva', '( %s -> A. s e. CC ( ( A x. s ) + B ) e. CC )' % A)
    all2 = w.s([D(w, As, 'addcld', [a1c, z0], '( ( A x. 1 ) + 0 ) e. CC')], 'ralrimiva', '( %s -> A. s e. CC ( ( A x. 1 ) + 0 ) e. CC )' % A)
    HS = L.HOLF('( s e. CC |-> ( ( A x. s ) + B ) )', 'CC')
    HZ = L.HOLF('( z e. CC |-> ( ( A x. z ) + B ) )', 'CC')
    ent = w.s([w.s([all1, w.s([dadd, all2], 'jca', '( %s -> ( ( CC _D ( s e. CC |-> ( ( A x. s ) + B ) ) ) = ( s e. CC |-> ( ( A x. 1 ) + 0 ) ) /\\ A. s e. CC ( ( A x. 1 ) + 0 ) e. CC ) )' % A)],
                   'jca', '( %s -> ( A. s e. CC ( ( A x. s ) + B ) e. CC /\\ ( ( CC _D ( s e. CC |-> ( ( A x. s ) + B ) ) ) = ( s e. CC |-> ( ( A x. 1 ) + 0 ) ) /\\ A. s e. CC ( ( A x. 1 ) + 0 ) e. CC ) ) )' % A),
               w.inst('z6ehdv')], 'syl', '( %s -> %s )' % (A, HS))
    cb = w.s([w.s([w.s([], 'oveq2', '( s = z -> ( A x. s ) = ( A x. z ) )')], 'oveq1d', '( s = z -> ( ( A x. s ) + B ) = ( ( A x. z ) + B ) )')],
             'cbvmptv', '( s e. CC |-> ( ( A x. s ) + B ) ) = ( z e. CC |-> ( ( A x. z ) + B ) )')
    tr = w.s([cb, w.inst('z6ehtr')], 'ax-mp', '( %s <-> %s )' % (HS, HZ))
    entz = w.s([ent, tr], 'sylib', '( %s -> %s )' % (A, HZ))
    w.qed([w.s([entz, op], 'jca', '( %s -> ( %s /\\ D e. ( TopOpen ` CCfld ) ) )' % (A, HZ)), w.inst('zl2hent')], 'syl', L.STATEMENTS['zl3haff'])
    go(w)


# ---------------------------------------------------------------- zl3hco
if __name__ == '__main__' and want('zl3hco'):
    w = W('zl3hco', 'The composition of holomorphic maps is holomorphic ( ~ cncfco , ~ dvcobr ).')
    A, C = ante_of('zl3hco')
    MAP = '( z e. D |-> ( F ` ( G ` z ) ) )'
    hF = D(w, A, 'simp1', [], L.HOLF('F', 'E')); hG = D(w, A, 'simp2', [], L.HOLF('G', 'D'))
    gall = D(w, A, 'simp3', [], 'A. v e. D ( G ` v ) e. E')
    fE = D(w, A, 'simpld', [hF], 'F e. ( E -cn-> CC )'); fEd = D(w, A, 'simprd', [hF], 'E C_ dom ( CC _D F )')
    gD = D(w, A, 'simpld', [hG], 'G e. ( D -cn-> CC )'); gDd = D(w, A, 'simprd', [hG], 'D C_ dom ( CC _D G )')
    Ff = w.s([fE, w.inst('cncff')], 'syl', '( %s -> F : E --> CC )' % A)
    Gf = w.s([gD, w.inst('cncff')], 'syl', '( %s -> G : D --> CC )' % A)
    Gfn = w.s([Gf, w.inst('ffn')], 'syl', '( %s -> G Fn D )' % A)
    GDE = w.s([Gfn, gall], 'jca', '( %s -> ( G Fn D /\\ A. v e. D ( G ` v ) e. E ) )' % A)
    GDE = w.s([GDE, w.s([], 'ffnfv', '( G : D --> E <-> ( G Fn D /\\ A. v e. D ( G ` v ) e. E ) )')], 'sylibr', '( %s -> G : D --> E )' % A)
    Ess = w.s([fE, w.inst('cncfrss')], 'syl', '( %s -> E C_ CC )' % A)
    Dss = w.s([gD, w.inst('cncfrss')], 'syl', '( %s -> D C_ CC )' % A)
    comp = w.s([Ff, GDE, w.inst('fcompt')], 'syl2anc', '( %s -> ( F o. G ) = %s )' % (A, MAP))
    gcont = w.s([GDE, w.s([Ess, gD, w.inst('cncfcdm')], 'syl2anc', '( %s -> ( G e. ( D -cn-> E ) <-> G : D --> E ) )' % A)], 'mpbird', '( %s -> G e. ( D -cn-> E ) )' % A)
    cco = w.s([gcont, fE], 'cncfco', '( %s -> ( F o. G ) e. ( D -cn-> CC ) )' % A)
    cont = w.s([cco, comp], 'eqeltrrd', '( %s -> %s e. ( D -cn-> CC ) )' % (A, MAP))
    Ac = '( %s /\\ c e. D )' % A
    cD = D(w, Ac, 'simpr', [], 'c e. D')
    gcE = D(w, Ac, 'ffvelcdmd', [D(w, Ac, 'adantr', [GDE], 'G : D --> E'), cD], '( G ` c ) e. E')
    gcd = D(w, Ac, 'sseldd', [D(w, Ac, 'adantr', [fEd], 'E C_ dom ( CC _D F )'), gcE], '( G ` c ) e. dom ( CC _D F )')
    cdd = D(w, Ac, 'sseldd', [D(w, Ac, 'adantr', [gDd], 'D C_ dom ( CC _D G )'), cD], 'c e. dom ( CC _D G )')
    funF = w.s([w.s([], 'dvfcn', '( CC _D F ) : dom ( CC _D F ) --> CC'), w.inst('ffun')], 'ax-mp', 'Fun ( CC _D F )')
    funG = w.s([w.s([], 'dvfcn', '( CC _D G ) : dom ( CC _D G ) --> CC'), w.inst('ffun')], 'ax-mp', 'Fun ( CC _D G )')
    K = '( ( CC _D F ) ` ( G ` c ) )'; Lc = '( ( CC _D G ) ` c )'
    bf = w.s([gcd, w.s([funF, w.inst('funfvbrb')], 'ax-mp', '( ( G ` c ) e. dom ( CC _D F ) <-> ( G ` c ) ( CC _D F ) %s )' % K)], 'sylib', '( %s -> ( G ` c ) ( CC _D F ) %s )' % (Ac, K))
    bg = w.s([cdd, w.s([funG, w.inst('funfvbrb')], 'ax-mp', '( c e. dom ( CC _D G ) <-> c ( CC _D G ) %s )' % Lc)], 'sylib', '( %s -> c ( CC _D G ) %s )' % (Ac, Lc))
    ssCC = w.s([w.s([], 'ssid', 'CC C_ CC')], 'a1i', '( %s -> CC C_ CC )' % Ac)
    br = w.s([D(w, Ac, 'adantr', [Ff], 'F : E --> CC'), D(w, Ac, 'adantr', [Ess], 'E C_ CC'), D(w, Ac, 'adantr', [GDE], 'G : D --> E'), D(w, Ac, 'adantr', [Dss], 'D C_ CC'),
              ssCC, ssCC, bf, bg, w.s([], 'eqid', '( TopOpen ` CCfld ) = ( TopOpen ` CCfld )')], 'dvcobr', '( %s -> c ( CC _D ( F o. G ) ) ( %s x. %s ) )' % (Ac, K, Lc))
    cdm = w.s([w.s([w.s([], 'reldv', 'Rel ( CC _D ( F o. G ) )')], 'a1i', '( %s -> Rel ( CC _D ( F o. G ) ) )' % Ac), br, w.inst('releldm')], 'syl2anc',
              '( %s -> c e. dom ( CC _D ( F o. G ) ) )' % Ac)
    ss = w.s([w.s([cdm], 'ex', '( %s -> ( c e. D -> c e. dom ( CC _D ( F o. G ) ) ) )' % A)], 'ssrdv', '( %s -> D C_ dom ( CC _D ( F o. G ) ) )' % A)
    dmq = w.s([w.s([comp], 'oveq2d', '( %s -> ( CC _D ( F o. G ) ) = ( CC _D %s ) )' % (A, MAP))], 'dmeqd', '( %s -> dom ( CC _D ( F o. G ) ) = dom ( CC _D %s ) )' % (A, MAP))
    ss2 = w.s([ss, dmq], 'sseqtrd', '( %s -> D C_ dom ( CC _D %s ) )' % (A, MAP))
    w.qed([cont, ss2], 'jca', L.STATEMENTS['zl3hco'])
    go(w)


# ---------------------------------------------------------------- section C: the closed form FL
LPI = '( log ` _pi )'
HALF = '( 1 / 2 )'
NH = '-u ( 1 / 2 )'
DQ = L.DQ
HP = "( `' Re \" ( 0 (,) +oo ) )"
GM = '( z e. %s |-> ( _G ` z ) )' % HP
AFF = {'0': (LPI, '( %s x. %s )' % (NH, LPI)), '1': (NH, '( ( 1 + P ) / 2 )'), '2': (HALF, '( P / 2 )'), '3': (HALF, '( ( P + 2 ) / 2 )')}
AM = {k: '( a e. %s |-> ( ( %s x. a ) + %s ) )' % (DQ, c, d) for k, (c, d) in AFF.items()}
AV = lambda k, x: '( ( %s x. %s ) + %s )' % (AFF[k][0], x, AFF[k][1])
H1 = '( b e. %s |-> ( exp ` ( %s ` b ) ) )' % (DQ, AM['0'])
H2 = '( b e. %s |-> ( %s ` ( %s ` b ) ) )' % (DQ, GM, AM['1'])
H3 = '( b e. %s |-> ( %s ` ( %s ` b ) ) )' % (DQ, GM, AM['3'])
H4 = '( c e. %s |-> ( ( %s ` c ) / ( %s ` c ) ) )' % (DQ, AM['2'], H3)
H5 = '( d e. %s |-> ( ( %s ` d ) x. ( %s ` d ) ) )' % (DQ, H2, H4)
H6 = '( y e. %s |-> ( ( %s ` y ) x. ( %s ` y ) ) )' % (DQ, H1, H5)


class Ctx:
    """facts in a context ( A /\\ x e. DQ ) with A = ( P e. RR /\\ 0 <_ P )"""
    def __init__(self, w, A, x, C=None, pr=None, p0=None, mem=None):
        self.w, self.x = w, x
        if C is None:
            self.C = C = '( %s /\\ %s e. %s )' % (A, x, DQ)
            self.pr = D(w, C, 'simpll', [], 'P e. RR'); self.p0 = D(w, C, 'simplr', [], '0 <_ P')
        else:
            self.C = C
            self.pr, self.p0 = pr, p0
        n1 = w.s([w.s([w.s([], 'neg1rr', '-u 1 e. RR')], 'rexri', '-u 1 e. RR*')], 'a1i', '( %s -> -u 1 e. RR* )' % C)
        p1 = w.s([w.s([w.s([], '1re', '1 e. RR')], 'rexri', '1 e. RR*')], 'a1i', '( %s -> 1 e. RR* )' % C)
        memst = mem if mem is not None else D(w, C, 'simpr', [], '%s e. %s' % (x, DQ))
        mem = w.s([memst, w.s([n1, p1, w.inst('z6melst')], 'syl2anc',
                  '( %s -> ( %s e. %s <-> ( %s e. CC /\\ ( -u 1 < ( Re ` %s ) /\\ ( Re ` %s ) < 1 ) ) ) )' % (C, x, DQ, x, x, x))], 'mpbid',
                  '( %s -> ( %s e. CC /\\ ( -u 1 < ( Re ` %s ) /\\ ( Re ` %s ) < 1 ) ) )' % (C, x, x, x))
        self.mem = memst
        self.xc = D(w, C, 'simpld', [mem], '%s e. CC' % x)
        lr = D(w, C, 'simprd', [mem], '( -u 1 < ( Re ` %s ) /\\ ( Re ` %s ) < 1 )' % (x, x))
        self.lo = D(w, C, 'simpld', [lr], '-u 1 < ( Re ` %s )' % x); self.hi = D(w, C, 'simprd', [lr], '( Re ` %s ) < 1' % x)
        self.rx = D(w, C, 'recld', [self.xc], '( Re ` %s ) e. RR' % x)
        self.cl = Closure(w, C, {'P': ('RR', self.pr), '( Re ` %s )' % x: ('RR', self.rx)})
        self.pc = D(w, C, 'recnd', [self.pr], 'P e. CC')
        self.c1 = a1(w, C, 'ax-1cn', '1 e. CC'); self.c2 = a1(w, C, '2cn', '2 e. CC')
        self.n2 = a1(w, C, '2ne0', '2 =/= 0')
        self.hc = a1(w, C, 'halfcn', '( 1 / 2 ) e. CC'); self.hr = a1(w, C, 'halfre', '( 1 / 2 ) e. RR')
        self.nhr = D(w, C, 'renegcld', [self.hr], '%s e. RR' % NH); self.nhc = D(w, C, 'recnd', [self.nhr], '%s e. CC' % NH)

    def rcoef(self, k):
        """( C -> coefficient e. RR ), ( C -> constant e. RR ) for k in 1 2 3"""
        w, C = self.w, self.C
        c, d = AFF[k]
        cr = self.nhr if c == NH else self.hr
        if k == '1':
            dr = D(w, C, 'rehalfcld', [D(w, C, 'readdcld', [a1(w, C, '1re', '1 e. RR'), self.pr], '( 1 + P ) e. RR')], '%s e. RR' % d)
        elif k == '2':
            dr = D(w, C, 'rehalfcld', [self.pr], '%s e. RR' % d)
        else:
            dr = D(w, C, 'rehalfcld', [D(w, C, 'readdcld', [self.pr, a1(w, C, '2re', '2 e. RR')], '( P + 2 ) e. RR')], '%s e. RR' % d)
        return cr, dr

    def re_aff(self, k):
        """( C -> ( Re ` AV k x ) = ( ( c x. ( Re ` x ) ) + d ) )"""
        w, C, x = self.w, self.C, self.x
        c, d = AFF[k]
        cr, dr = self.rcoef(k)
        cx = D(w, C, 'mulcld', [D(w, C, 'recnd', [cr], '%s e. CC' % c), self.xc], '( %s x. %s ) e. CC' % (c, x))
        e1 = E(w, C, 'readdd', [cx, D(w, C, 'recnd', [dr], '%s e. CC' % d)], '( Re ` %s )' % AV(k, x), '( ( Re ` ( %s x. %s ) ) + ( Re ` %s ) )' % (c, x, d))
        e2 = E(w, C, 'oveq12d', [E(w, C, 'remul2d', [cr, self.xc], '( Re ` ( %s x. %s ) )' % (c, x), '( %s x. ( Re ` %s ) )' % (c, x)),
                                 w.s([dr, w.inst('rered')], 'syl', '( %s -> ( Re ` %s ) = %s )' % (C, d, d))],
               '( ( Re ` ( %s x. %s ) ) + ( Re ` %s ) )' % (c, x, d), '( ( %s x. ( Re ` %s ) ) + %s )' % (c, x, d))
        return w.s([e1, e2], 'eqtrd', '( %s -> ( Re ` %s ) = ( ( %s x. ( Re ` %s ) ) + %s ) )' % (C, AV(k, x), c, x, d))

    def aff_val(self, k):
        """( C -> ( AM k ` x ) = AV k x ), and ( C -> AV k x e. CC )"""
        w, C, x = self.w, self.C, self.x
        st, val = mptv(w, C, 'a', DQ, AV(k, 'a'), x, self.mem, closure=None)
        return st

    def in_hp(self, k):
        """( C -> AV k x e. HP ) for k = 1, 3"""
        w, C, x = self.w, self.C, self.x
        c, d = AFF[k]
        cr, dr = self.rcoef(k)
        cl = Closure(w, C, {'P': ('RR', self.pr), '( Re ` %s )' % x: ('RR', self.rx)})
        pos = linarith(w, C, [self.lo, self.hi, self.p0], '0 < ( ( %s x. ( Re ` %s ) ) + %s )' % (c, x, d), closure=cl)
        pos2 = w.s([pos, self.re_aff(k)], 'breqtrrd', '( %s -> 0 < ( Re ` %s ) )' % (C, AV(k, x)))
        vc = D(w, C, 'addcld', [D(w, C, 'mulcld', [D(w, C, 'recnd', [cr], '%s e. CC' % c), self.xc], '( %s x. %s ) e. CC' % (c, x)),
                                D(w, C, 'recnd', [dr], '%s e. CC' % d)], '%s e. CC' % AV(k, x))
        z0 = w.s([w.s([w.s([], '0re', '0 e. RR')], 'rexri', '0 e. RR*')], 'a1i', '( %s -> 0 e. RR* )' % C)
        pinf = w.s([w.s([], 'pnfxr', '+oo e. RR*')], 'a1i', '( %s -> +oo e. RR* )' % C)
        lt = w.s([D(w, C, 'recld', [vc], '( Re ` %s ) e. RR' % AV(k, x)), w.inst('ltpnf')], 'syl', '( %s -> ( Re ` %s ) < +oo )' % (C, AV(k, x)))
        bi = w.s([z0, pinf, w.inst('z6melst')], 'syl2anc', '( %s -> ( %s e. %s <-> ( %s e. CC /\\ ( 0 < ( Re ` %s ) /\\ ( Re ` %s ) < +oo ) ) ) )' % (
            C, AV(k, x), HP, AV(k, x), AV(k, x), AV(k, x)))
        m = w.s([vc, w.s([pos2, lt], 'jca', '( %s -> ( 0 < ( Re ` %s ) /\\ ( Re ` %s ) < +oo ) )' % (C, AV(k, x), AV(k, x)))], 'jca',
                '( %s -> ( %s e. CC /\\ ( 0 < ( Re ` %s ) /\\ ( Re ` %s ) < +oo ) ) )' % (C, AV(k, x), AV(k, x), AV(k, x)))
        return w.s([m, bi], 'mpbird', '( %s -> %s e. %s )' % (C, AV(k, x), HP)), vc, pos2


def ident_iii(cx, x):
    """( C -> ( ( x + P ) / 2 ) = AV 2 x )"""
    w, C = cx.w, cx.C
    e1 = E(w, C, 'divdird', [cx.xc, cx.pc, cx.c2, cx.n2], '( ( %s + P ) / 2 )' % x, '( ( %s / 2 ) + ( P / 2 ) )' % x)
    e2 = E(w, C, 'oveq1d', [E(w, C, 'divrec2d', [cx.xc, cx.c2, cx.n2], '( %s / 2 )' % x, '( ( 1 / 2 ) x. %s )' % x)],
           '( ( %s / 2 ) + ( P / 2 ) )' % x, AV('2', x))
    return w.s([e1, e2], 'eqtrd', '( %s -> ( ( %s + P ) / 2 ) = %s )' % (C, x, AV('2', x)))


def ident_iv(cx, x):
    """( C -> ( ( ( x + P ) / 2 ) + 1 ) = AV 3 x )"""
    from lin import lineq
    w, C = cx.w, cx.C
    U = '( ( %s + P ) / 2 )' % x
    e1 = E(w, C, 'oveq1d', [ident_iii(cx, x)], '( %s + 1 )' % U, '( %s + 1 )' % AV('2', x))
    hx = D(w, C, 'mulcld', [cx.hc, cx.xc], '( ( 1 / 2 ) x. %s ) e. CC' % x)
    p2 = D(w, C, 'recnd', [D(w, C, 'rehalfcld', [cx.pr], '( P / 2 ) e. RR')], '( P / 2 ) e. CC')
    e2 = E(w, C, 'addassd', [hx, p2, cx.c1], '( %s + 1 )' % AV('2', x), '( ( ( 1 / 2 ) x. %s ) + ( ( P / 2 ) + 1 ) )' % x)
    e3 = E(w, C, 'oveq2d', [lineq(w, C, '( ( P / 2 ) + 1 )', '( ( P + 2 ) / 2 )', closure=Closure(w, C, {'P': ('RR', cx.pr)}))],
           '( ( ( 1 / 2 ) x. %s ) + ( ( P / 2 ) + 1 ) )' % x, AV('3', x))
    return chain(w, C, ['( %s + 1 )' % U, '( %s + 1 )' % AV('2', x), '( ( ( 1 / 2 ) x. %s ) + ( ( P / 2 ) + 1 ) )' % x, AV('3', x)], [e1, e2, e3])


def ident_ii(cx, x):
    """( C -> ( ( ( 1 - x ) + P ) / 2 ) = AV 1 x )"""
    w, C = cx.w, cx.C
    T0 = '( ( ( 1 - %s ) + P ) / 2 )' % x
    T1 = '( ( ( 1 + P ) - %s ) / 2 )' % x
    T2 = '( ( ( 1 + P ) / 2 ) - ( %s / 2 ) )' % x
    T3 = '( ( ( 1 + P ) / 2 ) + -u ( %s / 2 ) )' % x
    T4 = '( -u ( %s / 2 ) + ( ( 1 + P ) / 2 ) )' % x
    T5 = '( -u ( ( 1 / 2 ) x. %s ) + ( ( 1 + P ) / 2 ) )' % x
    T6 = AV('1', x)
    opc = D(w, C, 'addcld', [cx.c1, cx.pc], '( 1 + P ) e. CC')
    x2 = D(w, C, 'divcld', [cx.xc, cx.c2, cx.n2], '( %s / 2 ) e. CC' % x)
    op2 = D(w, C, 'divcld', [opc, cx.c2, cx.n2], '( ( 1 + P ) / 2 ) e. CC')
    e1 = E(w, C, 'oveq1d', [w.s([E(w, C, 'addsubd', [cx.c1, cx.pc, cx.xc], '( ( 1 + P ) - %s )' % x, '( ( 1 - %s ) + P )' % x)], 'eqcomd',
                                '( %s -> ( ( 1 - %s ) + P ) = ( ( 1 + P ) - %s ) )' % (C, x, x))], T0, T1)
    e2 = E(w, C, 'divsubdird', [opc, cx.xc, cx.c2, cx.n2], T1, T2)
    e3 = w.s([E(w, C, 'negsubd', [op2, x2], T3, T2)], 'eqcomd', '( %s -> %s = %s )' % (C, T2, T3))
    e4 = E(w, C, 'addcomd', [op2, D(w, C, 'negcld', [x2], '-u ( %s / 2 ) e. CC' % x)], T3, T4)
    e5 = E(w, C, 'oveq1d', [E(w, C, 'negeqd', [E(w, C, 'divrec2d', [cx.xc, cx.c2, cx.n2], '( %s / 2 )' % x, '( ( 1 / 2 ) x. %s )' % x)],
                                              '-u ( %s / 2 )' % x, '-u ( ( 1 / 2 ) x. %s )' % x)], T4, T5)
    e6 = w.s([E(w, C, 'mulneg1d', [cx.hc, cx.xc], '( %s x. %s )' % (NH, x), '-u ( ( 1 / 2 ) x. %s )' % x)], 'eqcomd',
             '( %s -> -u ( ( 1 / 2 ) x. %s ) = ( %s x. %s ) )' % (C, x, NH, x))
    e6 = E(w, C, 'oveq1d', [e6], T5, T6)
    return chain(w, C, [T0, T1, T2, T3, T4, T5, T6], [e1, e2, e3, e4, e5, e6])


def gm_val(cx, k):
    """( C -> ( GM ` ( AM k ` x ) ) = ( _G ` AV k x ) ), plus facts"""
    w, C, x = cx.w, cx.C, cx.x
    hp, vc, pos = cx.in_hp(k)
    av = cx.aff_val(k)
    e1 = E(w, C, 'fveq2d', [av], '( %s ` ( %s ` %s ) )' % (GM, AM[k], x), '( %s ` %s )' % (GM, AV(k, x)))
    e2, _ = mptv(w, C, 'z', HP, '( _G ` z )', AV(k, x), hp)
    eq = w.s([e1, e2], 'eqtrd', '( %s -> ( %s ` ( %s ` %s ) ) = ( _G ` %s ) )' % (C, GM, AM[k], x, AV(k, x)))
    nn = w.s([w.s([vc, pos], 'jca', '( %s -> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (C, AV(k, x), AV(k, x))), w.inst('zrenn')], 'syl',
             '( %s -> %s e. ( CC \\ ( ZZ \\ NN ) ) )' % (C, AV(k, x)))
    return eq, nn, hp, av


def hol_to(w, A, F, G, hol, eq, Dm):
    """HOL(G, Dm) from hol: HOL(F, Dm) and eq: ( A -> F = G )"""
    c = w.s([eq, D(w, A, 'simpld', [hol], '%s e. ( %s -cn-> CC )' % (F, Dm))], 'eqeltrrd', '( %s -> %s e. ( %s -cn-> CC ) )' % (A, G, Dm))
    dm = w.s([w.s([eq], 'oveq2d', '( %s -> ( CC _D %s ) = ( CC _D %s ) )' % (A, F, G))], 'dmeqd', '( %s -> dom ( CC _D %s ) = dom ( CC _D %s ) )' % (A, F, G))
    d = w.s([D(w, A, 'simprd', [hol], '%s C_ dom ( CC _D %s )' % (Dm, F)), dm], 'sseqtrd', '( %s -> %s C_ dom ( CC _D %s ) )' % (A, Dm, G))
    return w.s([c, d], 'jca', '( %s -> %s )' % (A, L.HOLF(G, Dm)))


# ---------------------------------------------------------------- zl3qhol
if __name__ == '__main__' and want('zl3qhol'):
    w = W('zl3qhol', 'The symmetric Gamma ratio in closed form, ` pi ^ ( w - 1/2 ) Gamma ( ( 1 - w + P ) / 2 ) u / Gamma ( u + 1 ) ` with '
          '` u = ( w + P ) / 2 ` , is holomorphic on the strip ` -1 < Re w < 1 ` ( ~ zl3haff , ~ zl3hco , ~ z6gamhol , ~ holmul , ~ holdiv ).')
    A, C = ante_of('zl3qhol')
    pr = D(w, A, 'simpl', [], 'P e. RR')
    pc = D(w, A, 'recnd', [pr], 'P e. CC')
    dq = w.s([w.s([], 'z6mstopn', '%s e. ( TopOpen ` CCfld )' % DQ)], 'a1i', '( %s -> %s e. ( TopOpen ` CCfld ) )' % (A, DQ))
    hc = a1(w, A, 'halfcn', '( 1 / 2 ) e. CC'); nhc = D(w, A, 'negcld', [hc], '%s e. CC' % NH)
    c2 = a1(w, A, '2cn', '2 e. CC'); n2 = a1(w, A, '2ne0', '2 =/= 0'); c1 = a1(w, A, 'ax-1cn', '1 e. CC')
    lpc = w.s([w.s([w.s([], 'pirp', '_pi e. RR+'), w.inst('relogcl')], 'ax-mp', '%s e. RR' % LPI)], 'a1i', '( %s -> %s e. RR )' % (A, LPI))
    lpc = D(w, A, 'recnd', [lpc], '%s e. CC' % LPI)
    cst = {'0': (lpc, D(w, A, 'mulcld', [nhc, lpc], '%s e. CC' % AFF['0'][1])),
           '1': (nhc, D(w, A, 'divcld', [D(w, A, 'addcld', [c1, pc], '( 1 + P ) e. CC'), c2, n2], '%s e. CC' % AFF['1'][1])),
           '2': (hc, D(w, A, 'divcld', [pc, c2, n2], '%s e. CC' % AFF['2'][1])),
           '3': (hc, D(w, A, 'divcld', [D(w, A, 'addcld', [pc, c2], '( P + 2 ) e. CC'), c2, n2], '%s e. CC' % AFF['3'][1]))}
    hol = {}
    for k in '0123':
        c, d = AFF[k]
        h = w.s([w.s([w.s(list(cst[k]), 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A, c, d)), dq], 'jca',
                     '( %s -> ( ( %s e. CC /\\ %s e. CC ) /\\ %s e. ( TopOpen ` CCfld ) ) )' % (A, c, d, DQ)), w.inst('zl3haff')], 'syl',
                '( %s -> %s )' % (A, L.HOLF(AM[k], DQ)))
        hol[k] = h
    h1 = w.s([hol['0'], w.inst('z6hexp')], 'syl', '( %s -> %s )' % (A, L.HOLF(H1, DQ)))
    gh = w.s([w.s([], 'z6gamhol', L.HOLF(GM, HP))], 'a1i', '( %s -> %s )' % (A, L.HOLF(GM, HP)))

    def allhp(k):
        cx = Ctx(w, A, 'v')
        hp, vc, pos = cx.in_hp(k)
        av = cx.aff_val(k)
        m = w.s([av, hp], 'eqeltrd', '( %s -> ( %s ` v ) e. %s )' % (cx.C, AM[k], HP))
        return w.s([m], 'ralrimiva', '( %s -> A. v e. %s ( %s ` v ) e. %s )' % (A, DQ, AM[k], HP))
    h2 = w.s([gh, hol['1'], allhp('1'), w.inst('zl3hco')], 'syl3anc', '( %s -> %s )' % (A, L.HOLF(H2, DQ)))
    h3 = w.s([gh, hol['3'], allhp('3'), w.inst('zl3hco')], 'syl3anc', '( %s -> %s )' % (A, L.HOLF(H3, DQ)))
    cv = Ctx(w, A, 'v')
    h3v, _ = mptv(w, cv.C, 'b', DQ, '( %s ` ( %s ` b ) )' % (GM, AM['3']), 'v', cv.mem)
    g3, nn3, _, _ = gm_val(cv, '3')
    ne = w.s([w.s([h3v, g3], 'eqtrd', '( %s -> ( %s ` v ) = ( _G ` %s ) )' % (cv.C, H3, AV('3', 'v'))),
              w.s([nn3, w.inst('gamne0')], 'syl', '( %s -> ( _G ` %s ) =/= 0 )' % (cv.C, AV('3', 'v')))], 'neeqtrrd' if False else 'idi', 'x') if False else None
    gne = w.s([nn3, w.inst('gamne0')], 'syl', '( %s -> ( _G ` %s ) =/= 0 )' % (cv.C, AV('3', 'v')))
    ne = w.s([w.s([h3v, g3], 'eqtrd', '( %s -> ( %s ` v ) = ( _G ` %s ) )' % (cv.C, H3, AV('3', 'v'))), gne], 'eqnetrd', '( %s -> ( %s ` v ) =/= 0 )' % (cv.C, H3))
    allne = w.s([ne], 'ralrimiva', '( %s -> A. v e. %s ( %s ` v ) =/= 0 )' % (A, DQ, H3))
    h4 = w.s([hol['2'], h3, allne, w.inst('holdiv')], 'syl3anc', '( %s -> %s )' % (A, L.HOLF(H4, DQ)))
    h5 = w.s([h2, h4, w.inst('holmul')], 'syl2anc', '( %s -> %s )' % (A, L.HOLF(H5, DQ)))
    h6 = w.s([h1, h5, w.inst('holmul')], 'syl2anc', '( %s -> %s )' % (A, L.HOLF(H6, DQ)))
    # values at w
    cw = Ctx(w, A, 'w')
    C_ = cw.C
    # H1 ` w = pi ^c ( w - 1/2 )
    v1, _ = mptv(w, C_, 'b', DQ, '( exp ` ( %s ` b ) )' % AM['0'], 'w', cw.mem)
    a0 = cw.aff_val('0')
    lp = D(w, C_, 'recnd', [w.s([w.s([w.s([], 'pirp', '_pi e. RR+'), w.inst('relogcl')], 'ax-mp', '%s e. RR' % LPI)], 'a1i', '( %s -> %s e. RR )' % (C_, LPI))], '%s e. CC' % LPI)
    WH = '( w - ( 1 / 2 ) )'
    t1 = E(w, C_, 'subdird', [cw.xc, cw.hc, lp], '( %s x. %s )' % (WH, LPI), '( ( w x. %s ) - ( ( 1 / 2 ) x. %s ) )' % (LPI, LPI))
    t2 = E(w, C_, 'mulneg1d', [cw.hc, lp], AFF['0'][1], '-u ( ( 1 / 2 ) x. %s )' % LPI)
    t3 = E(w, C_, 'mulcomd', [lp, cw.xc], '( %s x. w )' % LPI, '( w x. %s )' % LPI)
    t4 = E(w, C_, 'oveq12d', [t3, t2], AV('0', 'w'), '( ( w x. %s ) + -u ( ( 1 / 2 ) x. %s ) )' % (LPI, LPI))
    t5 = E(w, C_, 'negsubd', [D(w, C_, 'mulcld', [cw.xc, lp], '( w x. %s ) e. CC' % LPI), D(w, C_, 'mulcld', [cw.hc, lp], '( ( 1 / 2 ) x. %s ) e. CC' % LPI)],
           '( ( w x. %s ) + -u ( ( 1 / 2 ) x. %s ) )' % (LPI, LPI), '( ( w x. %s ) - ( ( 1 / 2 ) x. %s ) )' % (LPI, LPI))
    tt = w.s([w.s([t4, t5], 'eqtrd', '( %s -> %s = ( ( w x. %s ) - ( ( 1 / 2 ) x. %s ) ) )' % (C_, AV('0', 'w'), LPI, LPI)), t1], 'eqtr4d',
             '( %s -> %s = ( %s x. %s ) )' % (C_, AV('0', 'w'), WH, LPI))
    cxe = w.s([a1(w, C_, 'picn', '_pi e. CC'), a1(w, C_, 'pine0', '_pi =/= 0'), D(w, C_, 'subcld', [cw.xc, cw.hc], '%s e. CC' % WH), w.inst('cxpef')], 'syl3anc',
              '( %s -> ( _pi ^c %s ) = ( exp ` ( %s x. %s ) ) )' % (C_, WH, WH, LPI))
    eH1 = chain(w, C_, ['( %s ` w )' % H1, '( exp ` ( %s ` w ) )' % AM['0'], '( exp ` %s )' % AV('0', 'w'), '( exp ` ( %s x. %s ) )' % (WH, LPI), '( _pi ^c %s )' % WH],
                [v1, E(w, C_, 'fveq2d', [a0], '( exp ` ( %s ` w ) )' % AM['0'], '( exp ` %s )' % AV('0', 'w')),
                 E(w, C_, 'fveq2d', [tt], '( exp ` %s )' % AV('0', 'w'), '( exp ` ( %s x. %s ) )' % (WH, LPI)), ('r', cxe)])
    # H2 ` w
    v2, _ = mptv(w, C_, 'b', DQ, '( %s ` ( %s ` b ) )' % (GM, AM['1']), 'w', cw.mem)
    g1, _, _, _ = gm_val(cw, '1')
    G1 = '( _G ` ( ( ( 1 - w ) + P ) / 2 ) )'
    eH2 = chain(w, C_, ['( %s ` w )' % H2, '( %s ` ( %s ` w ) )' % (GM, AM['1']), '( _G ` %s )' % AV('1', 'w'), G1],
                [v2, g1, ('r', E(w, C_, 'fveq2d', [ident_ii(cw, 'w')], G1, '( _G ` %s )' % AV('1', 'w')))])
    # H3 ` w, H4 ` w
    v3, _ = mptv(w, C_, 'b', DQ, '( %s ` ( %s ` b ) )' % (GM, AM['3']), 'w', cw.mem)
    g3w, _, _, _ = gm_val(cw, '3')
    U = '( ( w + P ) / 2 )'
    G3 = '( _G ` ( %s + 1 ) )' % U
    eH3 = chain(w, C_, ['( %s ` w )' % H3, '( %s ` ( %s ` w ) )' % (GM, AM['3']), '( _G ` %s )' % AV('3', 'w'), G3],
                [v3, g3w, ('r', E(w, C_, 'fveq2d', [ident_iv(cw, 'w')], G3, '( _G ` %s )' % AV('3', 'w')))])
    v4, _ = mptv(w, C_, 'c', DQ, '( ( %s ` c ) / ( %s ` c ) )' % (AM['2'], H3), 'w', cw.mem)
    a2 = cw.aff_val('2')
    e2u = w.s([a2, w.s([ident_iii(cw, 'w')], 'eqcomd', '( %s -> %s = %s )' % (C_, AV('2', 'w'), U))], 'eqtrd', '( %s -> ( %s ` w ) = %s )' % (C_, AM['2'], U))
    eH4 = w.s([v4, E(w, C_, 'oveq12d', [e2u, eH3], '( ( %s ` w ) / ( %s ` w ) )' % (AM['2'], H3), '( %s / %s )' % (U, G3))], 'eqtrd',
              '( %s -> ( %s ` w ) = ( %s / %s ) )' % (C_, H4, U, G3))
    v5, _ = mptv(w, C_, 'd', DQ, '( ( %s ` d ) x. ( %s ` d ) )' % (H2, H4), 'w', cw.mem)
    eH5 = w.s([v5, E(w, C_, 'oveq12d', [eH2, eH4], '( ( %s ` w ) x. ( %s ` w ) )' % (H2, H4), '( %s x. ( %s / %s ) )' % (G1, U, G3))], 'eqtrd',
              '( %s -> ( %s ` w ) = ( %s x. ( %s / %s ) ) )' % (C_, H5, G1, U, G3))
    body = E(w, C_, 'oveq12d', [eH1, eH5], '( ( %s ` w ) x. ( %s ` w ) )' % (H1, H5), L.FLB('w'))
    meq = w.s([body], 'mpteq2dva', '( %s -> ( w e. %s |-> ( ( %s ` w ) x. ( %s ` w ) ) ) = %s )' % (A, DQ, H1, H5, L.FL))
    cb = w.s([w.s([w.s([], 'fveq2', '( y = w -> ( %s ` y ) = ( %s ` w ) )' % (H1, H1)), w.s([], 'fveq2', '( y = w -> ( %s ` y ) = ( %s ` w ) )' % (H5, H5))],
                  'oveq12d', '( y = w -> ( ( %s ` y ) x. ( %s ` y ) ) = ( ( %s ` w ) x. ( %s ` w ) ) )' % (H1, H5, H1, H5))],
             'cbvmptv', '%s = ( w e. %s |-> ( ( %s ` w ) x. ( %s ` w ) ) )' % (H6, DQ, H1, H5))
    eq = w.s([w.s([cb], 'a1i', '( %s -> %s = ( w e. %s |-> ( ( %s ` w ) x. ( %s ` w ) ) ) )' % (A, H6, DQ, H1, H5)), meq], 'eqtrd', '( %s -> %s = %s )' % (A, H6, L.FL))
    fin = hol_to(w, A, H6, L.FL, h6, eq, DQ)
    w.lines[-1] = w.lines[-1].replace(w.lines[-1].split(':', 1)[0] + ':', 'qed:', 1)
    go(w)


def qq_facts(cx):
    """in a Ctx at x: ( C -> ( QQ ` x ) = ( FL ` x ) ), ( C -> ( FL ` x ) = FLB x ), ( C -> FLB x e. CC ) and the pieces"""
    w, C, x = cx.w, cx.C, cx.x
    QB = lambda v: L.QQP.split(' |-> ', 1)[1][:-2].replace(' w ', ' %s ' % v)
    qbody_w = L.QQP.split(' |-> ', 1)[1][:-2]
    qv, qval = mptv(w, C, 'w', 'CC', qbody_w, x, cx.xc)
    fv, fval = mptv(w, C, 'w', DQ, L.FLB('w'), x, cx.mem)
    assert fval == L.FLB(x), fval
    U = '( ( %s + P ) / 2 )' % x
    # -1 < Re U
    e3 = ident_iii(cx, x)
    uc = D(w, C, 'divcld', [D(w, C, 'addcld', [cx.xc, cx.pc], '( %s + P ) e. CC' % x), cx.c2, cx.n2], '%s e. CC' % U)
    reu = w.s([E(w, C, 'fveq2d', [e3], '( Re ` %s )' % U, '( Re ` %s )' % AV('2', x)), cx.re_aff('2')], 'eqtrd',
              '( %s -> ( Re ` %s ) = ( ( ( 1 / 2 ) x. ( Re ` %s ) ) + ( P / 2 ) ) )' % (C, U, x))
    lt = linarith(w, C, [cx.lo, cx.p0], '-u 1 < ( ( ( 1 / 2 ) x. ( Re ` %s ) ) + ( P / 2 ) )' % x, closure=cx.cl)
    ltu = w.s([lt, reu], 'breqtrrd', '( %s -> -u 1 < ( Re ` %s ) )' % (C, U))
    ig = w.s([uc, ltu, w.inst('zl3igp1')], 'syl2anc', '( %s -> ( 1/_G ` %s ) = ( %s / ( _G ` ( %s + 1 ) ) ) )' % (C, U, U, U))
    G1 = '( _G ` ( ( ( 1 - %s ) + P ) / 2 ) )' % x
    qf = E(w, C, 'oveq2d', [E(w, C, 'oveq2d', [ig], '( %s x. ( 1/_G ` %s ) )' % (G1, U), '( %s x. ( %s / ( _G ` ( %s + 1 ) ) ) )' % (G1, U, U))],
           qval, fval)
    qeq = chain(w, C, ['( %s ` %s )' % (L.QQP, x), qval, fval, '( %s ` %s )' % (L.FL, x)], [qv, qf, ('r', fv)])
    # FLB x e. CC
    hp1, vc1, pos1 = cx.in_hp('1')
    nn1 = w.s([w.s([vc1, pos1], 'jca', '( %s -> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (C, AV('1', x), AV('1', x))), w.inst('zrenn')], 'syl',
              '( %s -> %s e. ( CC \\ ( ZZ \\ NN ) ) )' % (C, AV('1', x)))
    a1m = w.s([ident_ii(cx, x), nn1], 'eqeltrd', '( %s -> ( ( ( 1 - %s ) + P ) / 2 ) e. ( CC \\ ( ZZ \\ NN ) ) )' % (C, x))
    hp3, vc3, pos3 = cx.in_hp('3')
    nn3 = w.s([w.s([vc3, pos3], 'jca', '( %s -> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (C, AV('3', x), AV('3', x))), w.inst('zrenn')], 'syl',
              '( %s -> %s e. ( CC \\ ( ZZ \\ NN ) ) )' % (C, AV('3', x)))
    a3m = w.s([ident_iv(cx, x), nn3], 'eqeltrd', '( %s -> ( %s + 1 ) e. ( CC \\ ( ZZ \\ NN ) ) )' % (C, U))
    g1c = w.s([a1m, w.inst('gamcl')], 'syl', '( %s -> %s e. CC )' % (C, G1))
    g3c = w.s([a3m, w.inst('gamcl')], 'syl', '( %s -> ( _G ` ( %s + 1 ) ) e. CC )' % (C, U))
    g3n = w.s([a3m, w.inst('gamne0')], 'syl', '( %s -> ( _G ` ( %s + 1 ) ) =/= 0 )' % (C, U))
    WH = '( %s - ( 1 / 2 ) )' % x
    pw = w.s([a1(w, C, 'picn', '_pi e. CC'), D(w, C, 'subcld', [cx.xc, cx.hc], '%s e. CC' % WH), w.inst('cxpcld') if False else None][:2], 'cxpcld', '( %s -> ( _pi ^c %s ) e. CC )' % (C, WH))
    q = D(w, C, 'divcld', [uc, g3c, g3n], '( %s / ( _G ` ( %s + 1 ) ) ) e. CC' % (U, U))
    flc = D(w, C, 'mulcld', [pw, D(w, C, 'mulcld', [g1c, q], '( %s x. ( %s / ( _G ` ( %s + 1 ) ) ) ) e. CC' % (G1, U, U))], '%s e. CC' % fval)
    return dict(qeq=qeq, fv=fv, flc=flc, U=U, G1=G1, g1c=g1c, g3c=g3c, g3n=g3n, uc=uc, pw=pw, a1m=a1m, a3m=a3m, WH=WH)


def ctx_from(w, A, x, lo, hi, xc, cxC):
    """( A -> x e. DQ ) from ( A -> x e. CC ), ( A -> -u 1 < ( Re ` x ) ), ( A -> ( Re ` x ) < 1 )"""
    n1 = w.s([w.s([w.s([], 'neg1rr', '-u 1 e. RR')], 'rexri', '-u 1 e. RR*')], 'a1i', '( %s -> -u 1 e. RR* )' % A)
    p1 = w.s([w.s([w.s([], '1re', '1 e. RR')], 'rexri', '1 e. RR*')], 'a1i', '( %s -> 1 e. RR* )' % A)
    bi = w.s([n1, p1, w.inst('z6melst')], 'syl2anc', '( %s -> ( %s e. %s <-> ( %s e. CC /\\ ( -u 1 < ( Re ` %s ) /\\ ( Re ` %s ) < 1 ) ) ) )' % (A, x, DQ, x, x, x))
    m = w.s([xc, w.s([lo, hi], 'jca', '( %s -> ( -u 1 < ( Re ` %s ) /\\ ( Re ` %s ) < 1 ) )' % (A, x, x))], 'jca',
            '( %s -> ( %s e. CC /\\ ( -u 1 < ( Re ` %s ) /\\ ( Re ` %s ) < 1 ) ) )' % (A, x, x, x))
    return w.s([m, bi], 'mpbird', '( %s -> %s e. %s )' % (A, x, DQ))


# ---------------------------------------------------------------- zl3qv
if __name__ == '__main__' and want('zl3qv'):
    w = W('zl3qv', 'On the strip ` -1 < Re Z < 1 ` the symmetric Gamma ratio ` QQ ( P ) ` equals its closed form ( ~ zl3igp1 ) and is a complex number.')
    A, Cc = ante_of('zl3qv')
    Pp = L.PP
    cx = Ctx(w, Pp, 'Z')
    f = qq_facts(cx)
    inner = w.s([f['qeq'], w.s([f['fv'], f['flc']], 'eqeltrd', '( %s -> ( %s ` Z ) e. CC )' % (cx.C, L.FL))], 'jca', '( %s -> %s )' % (cx.C, Cc))
    pp = D(w, A, 'simpl', [], Pp)
    zc = D(w, A, 'simpr1', [], 'Z e. CC'); lo = D(w, A, 'simpr2', [], '-u 1 < ( Re ` Z )'); hi = D(w, A, 'simpr3', [], '( Re ` Z ) < 1')
    zdq = ctx_from(w, A, 'Z', lo, hi, zc, None)
    w.qed([w.s([pp, zdq], 'jca', '( %s -> %s )' % (A, cx.C)), inner], 'syl', L.STATEMENTS['zl3qv'])
    go(w)


def modulus(cx, f):
    """( C -> ( abs ` ( FL ` x ) ) = ( ( _pi ^c ( ( Re ` x ) - ( 1 / 2 ) ) ) x. ( ( abs ` G1 ) x. ( ( abs ` U ) / ( abs ` G3 ) ) ) ) )"""
    w, C, x = cx.w, cx.C, cx.x
    U, G1, WH = f['U'], f['G1'], f['WH']
    G3 = '( _G ` ( %s + 1 ) )' % U
    PW = '( _pi ^c %s )' % WH
    Q = '( %s / %s )' % (U, G3)
    e0 = E(w, C, 'fveq2d', [f['fv']], '( abs ` ( %s ` %s ) )' % (L.FL, x), '( abs ` %s )' % L.FLB(x))
    qc = D(w, C, 'divcld', [f['uc'], f['g3c'], f['g3n']], '%s e. CC' % Q)
    e1 = E(w, C, 'absmuld', [f['pw'], D(w, C, 'mulcld', [f['g1c'], qc], '( %s x. %s ) e. CC' % (G1, Q))], '( abs ` %s )' % L.FLB(x),
           '( ( abs ` %s ) x. ( abs ` ( %s x. %s ) ) )' % (PW, G1, Q))
    e2 = E(w, C, 'absmuld', [f['g1c'], qc], '( abs ` ( %s x. %s ) )' % (G1, Q), '( ( abs ` %s ) x. ( abs ` %s ) )' % (G1, Q))
    e3 = E(w, C, 'absdivd', [f['uc'], f['g3c'], f['g3n']], '( abs ` %s )' % Q, '( ( abs ` %s ) / ( abs ` %s ) )' % (U, G3))
    e23 = w.s([e2, E(w, C, 'oveq2d', [e3], '( ( abs ` %s ) x. ( abs ` %s ) )' % (G1, Q), '( ( abs ` %s ) x. ( ( abs ` %s ) / ( abs ` %s ) ) )' % (G1, U, G3))], 'eqtrd',
              '( %s -> ( abs ` ( %s x. %s ) ) = ( ( abs ` %s ) x. ( ( abs ` %s ) / ( abs ` %s ) ) ) )' % (C, G1, Q, G1, U, G3))
    pic = w.s([w.s([], 'pirp', '_pi e. RR+')], 'a1i', '( %s -> _pi e. RR+ )' % C)
    whc = D(w, C, 'subcld', [cx.xc, cx.hc], '%s e. CC' % WH)
    e4 = w.s([pic, whc, w.inst('abscxp')], 'syl2anc', '( %s -> ( abs ` %s ) = ( _pi ^c ( Re ` %s ) ) )' % (C, PW, WH))
    e5 = w.s([E(w, C, 'resubd', [cx.xc, cx.hc], '( Re ` %s )' % WH, '( ( Re ` %s ) - ( Re ` ( 1 / 2 ) ) )' % x),
              E(w, C, 'oveq2d', [w.s([cx.hr, w.inst('rered')], 'syl', '( %s -> ( Re ` ( 1 / 2 ) ) = ( 1 / 2 ) )' % C)],
                '( ( Re ` %s ) - ( Re ` ( 1 / 2 ) ) )' % x, '( ( Re ` %s ) - ( 1 / 2 ) )' % x)], 'eqtrd', '( %s -> ( Re ` %s ) = ( ( Re ` %s ) - ( 1 / 2 ) ) )' % (C, WH, x))
    e45 = w.s([e4, E(w, C, 'oveq2d', [e5], '( _pi ^c ( Re ` %s ) )' % WH, '( _pi ^c ( ( Re ` %s ) - ( 1 / 2 ) ) )' % x)], 'eqtrd',
              '( %s -> ( abs ` %s ) = ( _pi ^c ( ( Re ` %s ) - ( 1 / 2 ) ) ) )' % (C, PW, x))
    RHS = '( ( _pi ^c ( ( Re ` %s ) - ( 1 / 2 ) ) ) x. ( ( abs ` %s ) x. ( ( abs ` %s ) / ( abs ` %s ) ) ) )' % (x, G1, U, G3)
    e6 = E(w, C, 'oveq12d', [e45, e23], '( ( abs ` %s ) x. ( abs ` ( %s x. %s ) ) )' % (PW, G1, Q), RHS)
    return chain(w, C, ['( abs ` ( %s ` %s ) )' % (L.FL, x), '( abs ` %s )' % L.FLB(x), '( ( abs ` %s ) x. ( abs ` ( %s x. %s ) ) )' % (PW, G1, Q), RHS], [e0, e1, e6])


def im_abs(cx, k):
    """( C -> ( abs ` ( Im ` AV k x ) ) = ( ( 1 / 2 ) x. ( abs ` ( Im ` x ) ) ) ) for k = 1, 2, 3"""
    w, C, x = cx.w, cx.C, cx.x
    c, d = AFF[k]
    cr, dr = cx.rcoef(k)
    cc = D(w, C, 'recnd', [cr], '%s e. CC' % c)
    cxm = D(w, C, 'mulcld', [cc, cx.xc], '( %s x. %s ) e. CC' % (c, x))
    e1 = E(w, C, 'imaddd', [cxm, D(w, C, 'recnd', [dr], '%s e. CC' % d)], '( Im ` %s )' % AV(k, x), '( ( Im ` ( %s x. %s ) ) + ( Im ` %s ) )' % (c, x, d))
    e2 = E(w, C, 'oveq12d', [E(w, C, 'immul2d', [cr, cx.xc], '( Im ` ( %s x. %s ) )' % (c, x), '( %s x. ( Im ` %s ) )' % (c, x)),
                             w.s([dr, w.inst('reim0')], 'syl', '( %s -> ( Im ` %s ) = 0 )' % (C, d))],
           '( ( Im ` ( %s x. %s ) ) + ( Im ` %s ) )' % (c, x, d), '( ( %s x. ( Im ` %s ) ) + 0 )' % (c, x))
    ix = D(w, C, 'imcld', [cx.xc], '( Im ` %s ) e. RR' % x)
    ixc = D(w, C, 'recnd', [ix], '( Im ` %s ) e. CC' % x)
    cix = D(w, C, 'mulcld', [cc, ixc], '( %s x. ( Im ` %s ) ) e. CC' % (c, x))
    e3 = E(w, C, 'addridd', [cix], '( ( %s x. ( Im ` %s ) ) + 0 )' % (c, x), '( %s x. ( Im ` %s ) )' % (c, x))
    im = chain(w, C, ['( Im ` %s )' % AV(k, x), '( ( Im ` ( %s x. %s ) ) + ( Im ` %s ) )' % (c, x, d), '( ( %s x. ( Im ` %s ) ) + 0 )' % (c, x),
                      '( %s x. ( Im ` %s ) )' % (c, x)], [e1, e2, e3])
    a1_ = E(w, C, 'fveq2d', [im], '( abs ` ( Im ` %s ) )' % AV(k, x), '( abs ` ( %s x. ( Im ` %s ) ) )' % (c, x))
    HI = '( ( 1 / 2 ) x. ( Im ` %s ) )' % x
    if c == NH:
        a2 = E(w, C, 'fveq2d', [E(w, C, 'mulneg1d', [cx.hc, ixc], '( %s x. ( Im ` %s ) )' % (NH, x), '-u %s' % HI)],
               '( abs ` ( %s x. ( Im ` %s ) ) )' % (c, x), '( abs ` -u %s )' % HI)
        a3 = E(w, C, 'absnegd', [D(w, C, 'mulcld', [cx.hc, ixc], '%s e. CC' % HI)], '( abs ` -u %s )' % HI, '( abs ` %s )' % HI)
        a1_ = chain(w, C, ['( abs ` ( Im ` %s ) )' % AV(k, x), '( abs ` ( %s x. ( Im ` %s ) ) )' % (c, x), '( abs ` -u %s )' % HI, '( abs ` %s )' % HI], [a1_, a2, a3])
    a4 = E(w, C, 'absmuld', [cx.hc, ixc], '( abs ` %s )' % HI, '( ( abs ` ( 1 / 2 ) ) x. ( abs ` ( Im ` %s ) ) )' % x)
    hp = w.s([w.s([], 'halfgt0', '0 < ( 1 / 2 )')], 'a1i', '( %s -> 0 < ( 1 / 2 ) )' % C)
    a5 = E(w, C, 'oveq1d', [E(w, C, 'absidd', [cx.hr, D(w, C, 'ltled', [a1(w, C, '0re', '0 e. RR'), cx.hr, hp], '0 <_ ( 1 / 2 )')], '( abs ` ( 1 / 2 ) )', '( 1 / 2 )')],
           '( ( abs ` ( 1 / 2 ) ) x. ( abs ` ( Im ` %s ) ) )' % x, '( ( 1 / 2 ) x. ( abs ` ( Im ` %s ) ) )' % x)
    return chain(w, C, ['( abs ` ( Im ` %s ) )' % AV(k, x), '( abs ` %s )' % HI, '( ( abs ` ( 1 / 2 ) ) x. ( abs ` ( Im ` %s ) ) )' % x,
                        '( ( 1 / 2 ) x. ( abs ` ( Im ` %s ) ) )' % x], [a1_, a4, a5])


def gcompare(cx, f, kv, relow):
    """zl3gmono at Z := a = ( ( ( 1 - x ) + P ) / 2 ), V := U (kv = '2') or U + 1 (kv = '3');
    relow: ( C -> Re-a-form <_ Re-V-form ) on the AV forms.  Returns the zl3gmono conclusion step and the Re/abs facts."""
    w, C, x = cx.w, cx.C, cx.x
    U = f['U']
    Aa = '( ( ( 1 - %s ) + P ) / 2 )' % x
    Vv = U if kv == '2' else '( %s + 1 )' % U
    ida = ident_ii(cx, x)
    idv = ident_iii(cx, x) if kv == '2' else ident_iv(cx, x)
    ac = D(w, C, 'eqeltrd', [ida, D(w, C, 'addcld', [D(w, C, 'mulcld', [cx.nhc, cx.xc], '( %s x. %s ) e. CC' % (NH, x)),
                                                     D(w, C, 'recnd', [cx.rcoef('1')[1]], '%s e. CC' % AFF['1'][1])], '%s e. CC' % AV('1', x))], '%s e. CC' % Aa)
    vc = D(w, C, 'eqeltrd', [idv, D(w, C, 'addcld', [D(w, C, 'mulcld', [cx.hc, cx.xc], '( %s x. %s ) e. CC' % (HALF, x)),
                                                     D(w, C, 'recnd', [cx.rcoef(kv)[1]], '%s e. CC' % AFF[kv][1])], '%s e. CC' % AV(kv, x))], '%s e. CC' % Vv)
    rea = w.s([E(w, C, 'fveq2d', [ida], '( Re ` %s )' % Aa, '( Re ` %s )' % AV('1', x)), cx.re_aff('1')], 'eqtrd',
              '( %s -> ( Re ` %s ) = ( ( %s x. ( Re ` %s ) ) + %s ) )' % (C, Aa, NH, x, AFF['1'][1]))
    rev = w.s([E(w, C, 'fveq2d', [idv], '( Re ` %s )' % Vv, '( Re ` %s )' % AV(kv, x)), cx.re_aff(kv)], 'eqtrd',
              '( %s -> ( Re ` %s ) = ( ( %s x. ( Re ` %s ) ) + %s ) )' % (C, Vv, HALF, x, AFF[kv][1]))
    ima = w.s([E(w, C, 'fveq2d', [E(w, C, 'fveq2d', [ida], '( Im ` %s )' % Aa, '( Im ` %s )' % AV('1', x))], '( abs ` ( Im ` %s ) )' % Aa, '( abs ` ( Im ` %s ) )' % AV('1', x)),
               im_abs(cx, '1')], 'eqtrd', '( %s -> ( abs ` ( Im ` %s ) ) = ( ( 1 / 2 ) x. ( abs ` ( Im ` %s ) ) ) )' % (C, Aa, x))
    imv = w.s([E(w, C, 'fveq2d', [E(w, C, 'fveq2d', [idv], '( Im ` %s )' % Vv, '( Im ` %s )' % AV(kv, x))], '( abs ` ( Im ` %s ) )' % Vv, '( abs ` ( Im ` %s ) )' % AV(kv, x)),
               im_abs(cx, kv)], 'eqtrd', '( %s -> ( abs ` ( Im ` %s ) ) = ( ( 1 / 2 ) x. ( abs ` ( Im ` %s ) ) ) )' % (C, Vv, x))
    imeq = w.s([ima, imv], 'eqtr4d', '( %s -> ( abs ` ( Im ` %s ) ) = ( abs ` ( Im ` %s ) ) )' % (C, Aa, Vv))
    RA = '( ( %s x. ( Re ` %s ) ) + %s )' % (NH, x, AFF['1'][1])
    RV = '( ( %s x. ( Re ` %s ) ) + %s )' % (HALF, x, AFF[kv][1])
    posa = linarith(w, C, [cx.lo, cx.hi, cx.p0], '0 < %s' % RA, closure=cx.cl)
    pa = w.s([posa, rea], 'breqtrrd', '( %s -> 0 < ( Re ` %s ) )' % (C, Aa))
    le = w.s([w.s([rea, relow], 'eqbrtrd', '( %s -> ( Re ` %s ) <_ %s )' % (C, Aa, RV)), rev], 'breqtrrd', '( %s -> ( Re ` %s ) <_ ( Re ` %s ) )' % (C, Aa, Vv))
    hz = w.s([w.s([ac, vc], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (C, Aa, Vv)), w.s([imeq, pa, le], '3jca',
             '( %s -> ( ( abs ` ( Im ` %s ) ) = ( abs ` ( Im ` %s ) ) /\\ 0 < ( Re ` %s ) /\\ ( Re ` %s ) <_ ( Re ` %s ) ) )' % (C, Aa, Vv, Aa, Aa, Vv))], 'jca',
             '( %s -> ( ( %s e. CC /\\ %s e. CC ) /\\ ( ( abs ` ( Im ` %s ) ) = ( abs ` ( Im ` %s ) ) /\\ 0 < ( Re ` %s ) /\\ ( Re ` %s ) <_ ( Re ` %s ) ) ) )' % (C, Aa, Vv, Aa, Vv, Aa, Aa, Vv))
    gm = w.s([hz, w.inst('zl3gmono')], 'syl', '( %s -> ( ( abs ` ( _G ` %s ) ) x. ( _G ` ( Re ` %s ) ) ) <_ ( ( abs ` ( _G ` %s ) ) x. ( _G ` ( Re ` %s ) ) ) )' % (C, Aa, Vv, Vv, Aa))
    return dict(gm=gm, rea=rea, rev=rev, pa=pa, le=le, Aa=Aa, Vv=Vv, RA=RA, RV=RV, ac=ac, vc=vc, imv=imv, idv=idv)


def edge_ctx(w, A, zc, lo, hi):
    if A.startswith('( ( P e. RR /\\ 0 <_ P ) /\\'):
        pr = D(w, A, 'simpll', [], 'P e. RR'); p0 = D(w, A, 'simplr', [], '0 <_ P')
    else:
        pr = D(w, A, 'simpl1', [], 'P e. RR'); p0 = D(w, A, 'simpl2', [], '0 <_ P')
    mem = ctx_from(w, A, 'Z', lo, hi, zc, None)
    return Ctx(w, None, 'Z', C=A, pr=pr, p0=p0, mem=mem)


def recip_gp1(cx, f, upos):
    """( C -> ( ( abs ` U ) / ( abs ` ( _G ` ( U + 1 ) ) ) ) = ( 1 / ( abs ` ( _G ` U ) ) ) ) from upos: ( C -> 0 < ( Re ` U ) )"""
    w, C = cx.w, cx.C
    U = f['U']
    G3 = '( _G ` ( %s + 1 ) )' % U
    um = w.s([w.s([f['uc'], upos], 'jca', '( %s -> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (C, U, U)), w.inst('zrenn')], 'syl', '( %s -> %s e. ( CC \\ ( ZZ \\ NN ) ) )' % (C, U))
    gp = w.s([um, w.inst('gamp1')], 'syl', '( %s -> %s = ( ( _G ` %s ) x. %s ) )' % (C, G3, U, U))
    guc = w.s([um, w.inst('gamcl')], 'syl', '( %s -> ( _G ` %s ) e. CC )' % (C, U))
    gun = w.s([um, w.inst('gamne0')], 'syl', '( %s -> ( _G ` %s ) =/= 0 )' % (C, U))
    AU, AG = '( abs ` %s )' % U, '( abs ` ( _G ` %s ) )' % U
    ur = D(w, C, 'abscld', [f['uc']], '%s e. RR' % AU)
    upr = D(w, C, 'ltletrd', [a1(w, C, '0re', '0 e. RR'), D(w, C, 'recld', [f['uc']], '( Re ` %s ) e. RR' % U), ur, upos,
                              w.s([f['uc'], w.inst('releabs')], 'syl', '( %s -> ( Re ` %s ) <_ %s )' % (C, U, AU))], '0 < %s' % AU)
    urp = D(w, C, 'elrpd', [ur, upr], '%s e. RR+' % AU)
    agrp = D(w, C, 'absrpcld', [guc, gun], '%s e. RR+' % AG)
    e1 = E(w, C, 'oveq2d', [w.s([E(w, C, 'fveq2d', [gp], '( abs ` %s )' % G3, '( abs ` ( ( _G ` %s ) x. %s ) )' % (U, U)),
                                 E(w, C, 'absmuld', [guc, f['uc']], '( abs ` ( ( _G ` %s ) x. %s ) )' % (U, U), '( %s x. %s )' % (AG, AU))], 'eqtrd',
                                '( %s -> ( abs ` %s ) = ( %s x. %s ) )' % (C, G3, AG, AU))], '( %s / ( abs ` %s ) )' % (AU, G3), '( %s / ( %s x. %s ) )' % (AU, AG, AU))
    urc = D(w, C, 'rpcnd', [urp], '%s e. CC' % AU)
    e2 = E(w, C, 'oveq1d', [w.s([E(w, C, 'mullidd', [urc], '( 1 x. %s )' % AU, AU)], 'eqcomd', '( %s -> %s = ( 1 x. %s ) )' % (C, AU, AU))],
           '( %s / ( %s x. %s ) )' % (AU, AG, AU), '( ( 1 x. %s ) / ( %s x. %s ) )' % (AU, AG, AU))
    e3 = E(w, C, 'divcan5rd', [a1(w, C, 'ax-1cn', '1 e. CC'), D(w, C, 'rpcnd', [agrp], '%s e. CC' % AG), urc, D(w, C, 'rpne0d', [agrp], '%s =/= 0' % AG),
                               D(w, C, 'rpne0d', [urp], '%s =/= 0' % AU)], '( ( 1 x. %s ) / ( %s x. %s ) )' % (AU, AG, AU), '( 1 / %s )' % AG)
    return chain(w, C, ['( %s / ( abs ` %s ) )' % (AU, G3), '( %s / ( %s x. %s ) )' % (AU, AG, AU), '( ( 1 x. %s ) / ( %s x. %s ) )' % (AU, AG, AU), '( 1 / %s )' % AG],
                 [e1, e2, e3]), agrp


# ---------------------------------------------------------------- zl3qey
if __name__ == '__main__' and want('zl3qey'):
    w = W('zl3qey', 'On the line ` Re Z = 1/2 ` the symmetric Gamma ratio has modulus at most ` 1 ` : its two Gamma arguments have equal real parts '
          'and opposite imaginary parts ( ~ zl3gmono ).')
    A, Cc = ante_of('zl3qey')
    zc = D(w, A, 'simprl', [], 'Z e. CC'); re = D(w, A, 'simprr', [], '( Re ` Z ) = ( 1 / 2 )')
    lo = w.s([linarith(w, A, [], '-u 1 < ( 1 / 2 )'), re], 'breqtrrd', '( %s -> -u 1 < ( Re ` Z ) )' % A)
    hi = w.s([re, w.s([w.s([], 'halflt1', '( 1 / 2 ) < 1')], 'a1i', '( %s -> ( 1 / 2 ) < 1 )' % A)], 'eqbrtrd', '( %s -> ( Re ` Z ) < 1 )' % A)
    cx = edge_ctx(w, A, zc, lo, hi)
    f = qq_facts(cx)
    ge = D(w, A, 'eqled', [cx.hr, w.s([re], 'eqcomd', '( %s -> ( 1 / 2 ) = ( Re ` Z ) )' % A)], '( 1 / 2 ) <_ ( Re ` Z )')
    le = D(w, A, 'eqled', [cx.rx, re], '( Re ` Z ) <_ ( 1 / 2 )')
    RA = '( ( %s x. ( Re ` Z ) ) + %s )' % (NH, AFF['1'][1]); RV = '( ( %s x. ( Re ` Z ) ) + %s )' % (HALF, AFF['2'][1])
    relow = linarith(w, A, [ge, le], '%s <_ %s' % (RA, RV), closure=cx.cl)
    g = gcompare(cx, f, '2', relow)
    from lin import lineq
    ravr = lineq(w, A, RA, RV, hyps=[ge, le], closure=cx.cl)
    reeq = chain(w, A, ['( Re ` %s )' % g['Aa'], RA, RV, '( Re ` %s )' % g['Vv']], [g['rea'], ravr, ('r', g['rev'])])
    U = f['U']
    upos0 = linarith(w, A, [ge, cx.p0], '0 < %s' % RV, closure=cx.cl)
    upos = w.s([upos0, g['rev']], 'breqtrrd', '( %s -> 0 < ( Re ` %s ) )' % (A, U))
    gU = w.s([w.s([D(w, A, 'recld', [f['uc']], '( Re ` %s ) e. RR' % U), upos], 'jca', '( %s -> ( ( Re ` %s ) e. RR /\\ 0 < ( Re ` %s ) ) )' % (A, U, U)),
              w.inst('gamrrp')], 'syl', '( %s -> ( _G ` ( Re ` %s ) ) e. RR+ )' % (A, U))
    GA, GU = '( abs ` ( _G ` %s ) )' % g['Aa'], '( abs ` ( _G ` %s ) )' % U
    gm2 = w.s([g['gm'], E(w, A, 'oveq2d', [E(w, A, 'fveq2d', [reeq], '( _G ` ( Re ` %s ) )' % g['Aa'], '( _G ` ( Re ` %s ) )' % U)],
                            '( %s x. ( _G ` ( Re ` %s ) ) )' % (GU, g['Aa']), '( %s x. ( _G ` ( Re ` %s ) ) )' % (GU, U))], 'breqtrd',
              '( %s -> ( %s x. ( _G ` ( Re ` %s ) ) ) <_ ( %s x. ( _G ` ( Re ` %s ) ) ) )' % (A, GA, U, GU, U))
    gac = w.s([f['a1m'], w.inst('gamcl')], 'syl', '( %s -> ( _G ` %s ) e. CC )' % (A, g['Aa']))
    rq, agrp = recip_gp1(cx, f, upos)
    GAr = D(w, A, 'abscld', [gac], '%s e. RR' % GA)
    gle = w.s([gm2, D(w, A, 'lemul1d', [GAr, D(w, A, 'rpred', [agrp], '%s e. RR' % GU), gU],
                      '( %s <_ %s <-> ( %s x. ( _G ` ( Re ` %s ) ) ) <_ ( %s x. ( _G ` ( Re ` %s ) ) ) )' % (GA, GU, GA, U, GU, U))], 'mpbird', '( %s -> %s <_ %s )' % (A, GA, GU))
    mod = modulus(cx, f)
    G3 = '( _G ` ( %s + 1 ) )' % U
    # pi ^c ( Re Z - 1/2 ) = 1
    e0 = E(w, A, 'oveq1d', [re], '( ( Re ` Z ) - ( 1 / 2 ) )', '( ( 1 / 2 ) - ( 1 / 2 ) )')
    e1 = E(w, A, 'subidd', [cx.hc], '( ( 1 / 2 ) - ( 1 / 2 ) )', '0')
    pw1 = chain(w, A, ['( _pi ^c ( ( Re ` Z ) - ( 1 / 2 ) ) )', '( _pi ^c ( ( 1 / 2 ) - ( 1 / 2 ) ) )', '( _pi ^c 0 )', '1'],
                [E(w, A, 'oveq2d', [e0], '( _pi ^c ( ( Re ` Z ) - ( 1 / 2 ) ) )', '( _pi ^c ( ( 1 / 2 ) - ( 1 / 2 ) ) )'),
                 E(w, A, 'oveq2d', [e1], '( _pi ^c ( ( 1 / 2 ) - ( 1 / 2 ) ) )', '( _pi ^c 0 )'),
                 w.s([w.s([w.s([], 'picn', '_pi e. CC'), w.inst('cxp0')], 'ax-mp', '( _pi ^c 0 ) = 1')], 'a1i', '( %s -> ( _pi ^c 0 ) = 1 )' % A)])
    M0 = '( ( _pi ^c ( ( Re ` Z ) - ( 1 / 2 ) ) ) x. ( %s x. ( ( abs ` %s ) / ( abs ` %s ) ) ) )' % (GA, U, G3)
    M1 = '( 1 x. ( %s x. ( 1 / %s ) ) )' % (GA, GU)
    e2 = E(w, A, 'oveq12d', [pw1, E(w, A, 'oveq2d', [rq], '( %s x. ( ( abs ` %s ) / ( abs ` %s ) ) )' % (GA, U, G3), '( %s x. ( 1 / %s ) )' % (GA, GU))], M0, M1)
    gaC = D(w, A, 'recnd', [GAr], '%s e. CC' % GA)
    e3 = E(w, A, 'mullidd', [D(w, A, 'mulcld', [gaC, D(w, A, 'reccld', [D(w, A, 'rpcnd', [agrp], '%s e. CC' % GU), D(w, A, 'rpne0d', [agrp], '%s =/= 0' % GU)],
                                                          '( 1 / %s ) e. CC' % GU)], '( %s x. ( 1 / %s ) ) e. CC' % (GA, GU))], M1, '( %s x. ( 1 / %s ) )' % (GA, GU))
    e4 = w.s([E(w, A, 'divrecd', [gaC, D(w, A, 'rpcnd', [agrp], '%s e. CC' % GU), D(w, A, 'rpne0d', [agrp], '%s =/= 0' % GU)], '( %s / %s )' % (GA, GU), '( %s x. ( 1 / %s ) )' % (GA, GU))],
             'eqcomd', '( %s -> ( %s x. ( 1 / %s ) ) = ( %s / %s ) )' % (A, GA, GU, GA, GU))
    mfin = chain(w, A, ['( abs ` ( %s ` Z ) )' % L.FL, M0, M1, '( %s x. ( 1 / %s ) )' % (GA, GU), '( %s / %s )' % (GA, GU)], [mod, e2, e3, e4])
    dl = w.s([gle, w.s([GAr, agrp, w.inst('divle1le')], 'syl2anc', '( %s -> ( ( %s / %s ) <_ 1 <-> %s <_ %s ) )' % (A, GA, GU, GA, GU))], 'mpbird', '( %s -> ( %s / %s ) <_ 1 )' % (A, GA, GU))
    w.qed([mfin, dl], 'eqbrtrd', L.STATEMENTS['zl3qey'])
    go(w)


def absU(cx, f, ge, le, p1):
    """( C -> ( abs ` U ) <_ ( ( abs ` ( Im ` x ) ) + 2 ) ) from -1/2 <_ Re x <_ 1/2 (ge, le) and P <_ 1 (p1)"""
    w, C, x = cx.w, cx.C, cx.x
    U = f['U']
    i3 = ident_iii(cx, x)
    reu = w.s([E(w, C, 'fveq2d', [i3], '( Re ` %s )' % U, '( Re ` %s )' % AV('2', x)), cx.re_aff('2')], 'eqtrd',
              '( %s -> ( Re ` %s ) = ( ( ( 1 / 2 ) x. ( Re ` %s ) ) + ( P / 2 ) ) )' % (C, U, x))
    RU = '( ( ( 1 / 2 ) x. ( Re ` %s ) ) + ( P / 2 ) )' % x
    l1 = linarith(w, C, [ge, le, cx.p0, p1], '-u 1 <_ %s' % RU, closure=cx.cl)
    l2 = linarith(w, C, [ge, le, cx.p0, p1], '%s <_ 1' % RU, closure=cx.cl)
    ru = D(w, C, 'recld', [f['uc']], '( Re ` %s ) e. RR' % U)
    b = w.s([w.s([w.s([l1, reu], 'breqtrrd', '( %s -> -u 1 <_ ( Re ` %s ) )' % (C, U)), w.s([reu, l2], 'eqbrtrd', '( %s -> ( Re ` %s ) <_ 1 )' % (C, U))], 'jca',
                 '( %s -> ( -u 1 <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ 1 ) )' % (C, U, U)),
             D(w, C, 'absled', [ru, a1(w, C, '1re', '1 e. RR')], '( ( abs ` ( Re ` %s ) ) <_ 1 <-> ( -u 1 <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ 1 ) )' % (U, U, U))],
            'mpbird', '( %s -> ( abs ` ( Re ` %s ) ) <_ 1 )' % (C, U))
    imu = w.s([E(w, C, 'fveq2d', [E(w, C, 'fveq2d', [i3], '( Im ` %s )' % U, '( Im ` %s )' % AV('2', x))], '( abs ` ( Im ` %s ) )' % U, '( abs ` ( Im ` %s ) )' % AV('2', x)),
               im_abs(cx, '2')], 'eqtrd', '( %s -> ( abs ` ( Im ` %s ) ) = ( ( 1 / 2 ) x. ( abs ` ( Im ` %s ) ) ) )' % (C, U, x))
    cr = w.s([f['uc'], w.inst('abscrle')], 'syl', '( %s -> ( abs ` %s ) <_ ( ( abs ` ( Re ` %s ) ) + ( abs ` ( Im ` %s ) ) ) )' % (C, U, U, U))
    AIU, AIX = '( abs ` ( Im ` %s ) )' % U, '( abs ` ( Im ` %s ) )' % x
    ix = D(w, C, 'imcld', [cx.xc], '( Im ` %s ) e. RR' % x)
    cl = Closure(w, C, {'( abs ` %s )' % U: ('RR', D(w, C, 'abscld', [f['uc']], '( abs ` %s ) e. RR' % U)),
                        '( abs ` ( Re ` %s ) )' % U: ('RR', D(w, C, 'abscld', [D(w, C, 'recnd', [ru], '( Re ` %s ) e. CC' % U)], '( abs ` ( Re ` %s ) ) e. RR' % U)),
                        AIU: ('RR', D(w, C, 'abscld', [D(w, C, 'recnd', [D(w, C, 'imcld', [f['uc']], '( Im ` %s ) e. RR' % U)], '( Im ` %s ) e. CC' % U)], '%s e. RR' % AIU)),
                        AIX: ('RR', D(w, C, 'abscld', [D(w, C, 'recnd', [ix], '( Im ` %s ) e. CC' % x)], '%s e. RR' % AIX))})
    ax0 = D(w, C, 'absge0d', [D(w, C, 'recnd', [ix], '( Im ` %s ) e. CC' % x)], '0 <_ %s' % AIX)
    imu_le = D(w, C, 'eqled', [cl.mem(AIU, 'RR'), imu], '%s <_ ( ( 1 / 2 ) x. %s )' % (AIU, AIX))
    return linarith(w, C, [cr, b, imu_le, ax0], '( abs ` %s ) <_ ( %s + 2 )' % (U, AIX), closure=cl)


# ---------------------------------------------------------------- zl3qex
if __name__ == '__main__' and want('zl3qex'):
    w = W('zl3qex', 'On the line ` Re Z = -1/2 ` the symmetric Gamma ratio is at most ` | Im Z | + 2 ` : ` Gamma ( ( 1 - Z + P ) / 2 ) ` and '
          '` Gamma ( ( Z + P ) / 2 + 1 ) ` have equal real parts ( ~ zl3gmono ), so the ratio is at most ` | u | / pi ` .')
    A, Cc = ante_of('zl3qex')
    zc = D(w, A, 'simprl', [], 'Z e. CC'); re = D(w, A, 'simprr', [], '( Re ` Z ) = -u ( 1 / 2 )')
    p1 = D(w, A, 'simpl3', [], 'P <_ 1')
    lo = w.s([linarith(w, A, [], '-u 1 < -u ( 1 / 2 )'), re], 'breqtrrd', '( %s -> -u 1 < ( Re ` Z ) )' % A)
    hi = w.s([re, linarith(w, A, [], '-u ( 1 / 2 ) < 1')], 'eqbrtrd', '( %s -> ( Re ` Z ) < 1 )' % A)
    cx = edge_ctx(w, A, zc, lo, hi)
    f = qq_facts(cx)
    ge = D(w, A, 'eqled', [cx.nhr, w.s([re], 'eqcomd', '( %s -> -u ( 1 / 2 ) = ( Re ` Z ) )' % A)], '-u ( 1 / 2 ) <_ ( Re ` Z )')
    le = D(w, A, 'eqled', [cx.rx, re], '( Re ` Z ) <_ -u ( 1 / 2 )')
    le2 = linarith(w, A, [le], '( Re ` Z ) <_ ( 1 / 2 )', closure=cx.cl)
    RA = '( ( %s x. ( Re ` Z ) ) + %s )' % (NH, AFF['1'][1]); RV = '( ( %s x. ( Re ` Z ) ) + %s )' % (HALF, AFF['3'][1])
    relow = linarith(w, A, [ge, le], '%s <_ %s' % (RA, RV), closure=cx.cl)
    g = gcompare(cx, f, '3', relow)
    from lin import lineq
    ravr = lineq(w, A, RA, RV, hyps=[ge, le], closure=cx.cl)
    reeq = chain(w, A, ['( Re ` %s )' % g['Aa'], RA, RV, '( Re ` %s )' % g['Vv']], [g['rea'], ravr, ('r', g['rev'])])
    U = f['U']; V1 = g['Vv']
    vpos0 = linarith(w, A, [ge, cx.p0], '0 < %s' % RV, closure=cx.cl)
    vpos = w.s([vpos0, g['rev']], 'breqtrrd', '( %s -> 0 < ( Re ` %s ) )' % (A, V1))
    gV = w.s([w.s([D(w, A, 'recld', [g['vc']], '( Re ` %s ) e. RR' % V1), vpos], 'jca', '( %s -> ( ( Re ` %s ) e. RR /\\ 0 < ( Re ` %s ) ) )' % (A, V1, V1)),
              w.inst('gamrrp')], 'syl', '( %s -> ( _G ` ( Re ` %s ) ) e. RR+ )' % (A, V1))
    GA, GV = '( abs ` ( _G ` %s ) )' % g['Aa'], '( abs ` ( _G ` %s ) )' % V1
    gm2 = w.s([g['gm'], E(w, A, 'oveq2d', [E(w, A, 'fveq2d', [reeq], '( _G ` ( Re ` %s ) )' % g['Aa'], '( _G ` ( Re ` %s ) )' % V1)],
                            '( %s x. ( _G ` ( Re ` %s ) ) )' % (GV, g['Aa']), '( %s x. ( _G ` ( Re ` %s ) ) )' % (GV, V1))], 'breqtrd',
              '( %s -> ( %s x. ( _G ` ( Re ` %s ) ) ) <_ ( %s x. ( _G ` ( Re ` %s ) ) ) )' % (A, GA, V1, GV, V1))
    GAr = D(w, A, 'abscld', [f['g1c']], '%s e. RR' % GA)
    GVr = D(w, A, 'abscld', [f['g3c']], '%s e. RR' % GV)
    gle = w.s([gm2, D(w, A, 'lemul1d', [GAr, GVr, gV], '( %s <_ %s <-> ( %s x. ( _G ` ( Re ` %s ) ) ) <_ ( %s x. ( _G ` ( Re ` %s ) ) ) )' % (GA, GV, GA, V1, GV, V1))],
              'mpbird', '( %s -> %s <_ %s )' % (A, GA, GV))
    mod = modulus(cx, f)
    AU = '( abs ` %s )' % U
    aur = D(w, A, 'abscld', [f['uc']], '%s e. RR' % AU)
    gvrp = D(w, A, 'absrpcld', [f['g3c'], f['g3n']], '%s e. RR+' % GV)
    Q = '( %s / %s )' % (AU, GV)
    qr = D(w, A, 'rerpdivcld', [aur, gvrp], '%s e. RR' % Q)
    q0 = D(w, A, 'divge0d', [aur, gvrp, D(w, A, 'absge0d', [f['uc']], '0 <_ %s' % AU)], '0 <_ %s' % Q)
    m1 = D(w, A, 'lemul1ad', [GAr, GVr, qr, q0, gle], '( %s x. %s ) <_ ( %s x. %s )' % (GA, Q, GV, Q))
    dc = E(w, A, 'divcan2d', [D(w, A, 'recnd', [aur], '%s e. CC' % AU), D(w, A, 'rpcnd', [gvrp], '%s e. CC' % GV), D(w, A, 'rpne0d', [gvrp], '%s =/= 0' % GV)],
           '( %s x. %s )' % (GV, Q), AU)
    m2 = w.s([m1, dc], 'breqtrd', '( %s -> ( %s x. %s ) <_ %s )' % (A, GA, Q, AU))
    EX = '( ( Re ` Z ) - ( 1 / 2 ) )'
    exr = D(w, A, 'resubcld', [cx.rx, cx.hr], '%s e. RR' % EX)
    exle = linarith(w, A, [le], '%s <_ 0' % EX, closure=cx.cl)
    one_pi = linarith(w, A, [w.s([w.s([], 'pigt3', '3 < _pi')], 'a1i', '( %s -> 3 < _pi )' % A)], '1 <_ _pi', closure=Closure(w, A, {'_pi': ('RR', a1(w, A, 'pire', '_pi e. RR'))}))
    pwle = w.s([w.s([a1(w, A, 'pire', '_pi e. RR'), one_pi], 'jca', '( %s -> ( _pi e. RR /\\ 1 <_ _pi ) )' % A),
                w.s([exr, a1(w, A, '0re', '0 e. RR')], 'jca', '( %s -> ( %s e. RR /\\ 0 e. RR ) )' % (A, EX)), exle, w.inst('cxplea')], 'syl3anc',
               '( %s -> ( _pi ^c %s ) <_ ( _pi ^c 0 ) )' % (A, EX))
    pw1 = w.s([pwle, w.s([w.s([w.s([], 'picn', '_pi e. CC'), w.inst('cxp0')], 'ax-mp', '( _pi ^c 0 ) = 1')], 'a1i', '( %s -> ( _pi ^c 0 ) = 1 )' % A)], 'breqtrd',
              '( %s -> ( _pi ^c %s ) <_ 1 )' % (A, EX))
    pwrp = D(w, A, 'rpcxpcld', [a1(w, A, 'pirp', '_pi e. RR+'), exr], '( _pi ^c %s ) e. RR+' % EX)
    Y = '( %s x. %s )' % (GA, Q)
    yr = D(w, A, 'remulcld', [GAr, qr], '%s e. RR' % Y)
    y0 = D(w, A, 'mulge0d', [GAr, qr, D(w, A, 'absge0d', [f['g1c']], '0 <_ %s' % GA), q0], '0 <_ %s' % Y)
    m3 = D(w, A, 'lemul12ad', [D(w, A, 'rpred', [pwrp], '( _pi ^c %s ) e. RR' % EX), a1(w, A, '1re', '1 e. RR'), yr, aur,
                               D(w, A, 'rpge0d', [pwrp], '0 <_ ( _pi ^c %s )' % EX), y0, pw1, m2], '( ( _pi ^c %s ) x. %s ) <_ ( 1 x. %s )' % (EX, Y, AU))
    m4 = w.s([m3, E(w, A, 'mullidd', [D(w, A, 'recnd', [aur], '%s e. CC' % AU)], '( 1 x. %s )' % AU, AU)], 'breqtrd', '( %s -> ( ( _pi ^c %s ) x. %s ) <_ %s )' % (A, EX, Y, AU))
    au = absU(cx, f, ge, le2, p1)
    fin1 = w.s([mod, m4], 'eqbrtrd', '( %s -> ( abs ` ( %s ` Z ) ) <_ %s )' % (A, L.FL, AU))
    w.qed([D(w, A, 'abscld', [w.s([f['fv'], f['flc']], 'eqeltrd', '( %s -> ( %s ` Z ) e. CC )' % (A, L.FL))], '( abs ` ( %s ` Z ) ) e. RR' % L.FL), aur,
           D(w, A, 'readdcld', [D(w, A, 'abscld', [D(w, A, 'recnd', [D(w, A, 'imcld', [zc], '( Im ` Z ) e. RR')], '( Im ` Z ) e. CC')], '( abs ` ( Im ` Z ) ) e. RR'),
                                a1(w, A, '2re', '2 e. RR')], '( ( abs ` ( Im ` Z ) ) + 2 ) e. RR'), fin1, au], 'letrd', L.STATEMENTS['zl3qex'])
    go(w)


def in_i100(w, C, t, rt, lo, hi, cl):
    """( C -> t e. ( ( 1 / ; ; 1 0 0 ) [,] 3 ) ) from linear bounds lo/hi (steps giving 1/100 <_ t, t <_ 3 via cl)"""
    I = L.I100
    h1 = w.s([w.s([w.s([w.s([], '1rp', '1 e. RR+'), w.s([w.s([w.s([w.s([], '1nn', '1 e. NN')], 'decnncl2', '; 1 0 e. NN')], 'decnncl2', '; ; 1 0 0 e. NN'), w.inst('nnrp')], 'ax-mp', '; ; 1 0 0 e. RR+'),
                          w.inst('rpdivcl')], 'mp2an', '( 1 / ; ; 1 0 0 ) e. RR+'), w.inst('rpre')], 'ax-mp', '( 1 / ; ; 1 0 0 ) e. RR')], 'a1i', '( %s -> ( 1 / ; ; 1 0 0 ) e. RR )' % C)
    bi = w.s([h1, a1(w, C, '3re', '3 e. RR'), w.inst('elicc2')], 'syl2anc', '( %s -> ( %s e. %s <-> ( %s e. RR /\\ ( 1 / ; ; 1 0 0 ) <_ %s /\\ %s <_ 3 ) ) )' % (C, t, I, t, t, t))
    return w.s([w.s([rt, lo, hi], '3jca', '( %s -> ( %s e. RR /\\ ( 1 / ; ; 1 0 0 ) <_ %s /\\ %s <_ 3 ) )' % (C, t, t, t)), bi], 'mpbird', '( %s -> %s e. %s )' % (C, t, I))


# ---------------------------------------------------------------- zl3qgb
if __name__ == '__main__' and want('zl3qgb'):
    w = W('zl3qgb', 'The symmetric Gamma ratio on ` -1/2 <_ Re Z <_ 1/2 ` : ` | QQ | <_ 2 D e ^ | Im Z | ` when ` D ` bounds the ratio of Gamma on '
          '` [ 1 / 100 , 3 ] ` ( ~ zl3gmono between ` ( 1 - Z + P ) / 2 ` and ` ( Z + P ) / 2 + 1 ` , ~ bvefge1p ).')
    A, Cc = ante_of('zl3qgb')
    I = L.I100
    HD = 'A. p e. %s A. q e. %s ( _G ` p ) <_ ( D x. ( _G ` q ) )' % (I, I)
    pp1 = D(w, A, 'simpll', [], L.PP1)
    pr = D(w, A, 'simp1d', [pp1], 'P e. RR'); p0 = D(w, A, 'simp2d', [pp1], '0 <_ P'); p1 = D(w, A, 'simp3d', [pp1], 'P <_ 1')
    dh = D(w, A, 'simplr', [], '( D e. RR+ /\\ %s )' % HD)
    drp = D(w, A, 'simpld', [dh], 'D e. RR+'); hall = D(w, A, 'simprd', [dh], HD)
    zc = D(w, A, 'simpr1', [], 'Z e. CC'); ge = D(w, A, 'simpr2', [], '-u ( 1 / 2 ) <_ ( Re ` Z )'); le = D(w, A, 'simpr3', [], '( Re ` Z ) <_ ( 1 / 2 )')
    rz = D(w, A, 'recld', [zc], '( Re ` Z ) e. RR')
    cl0 = Closure(w, A, {'( Re ` Z )': ('RR', rz)})
    lo = linarith(w, A, [ge], '-u 1 < ( Re ` Z )', closure=cl0); hi = linarith(w, A, [le], '( Re ` Z ) < 1', closure=cl0)
    mem = ctx_from(w, A, 'Z', lo, hi, zc, None)
    cx = Ctx(w, None, 'Z', C=A, pr=pr, p0=p0, mem=mem)
    f = qq_facts(cx)
    RA = '( ( %s x. ( Re ` Z ) ) + %s )' % (NH, AFF['1'][1]); RV = '( ( %s x. ( Re ` Z ) ) + %s )' % (HALF, AFF['3'][1])
    relow = linarith(w, A, [ge], '%s <_ %s' % (RA, RV), closure=cx.cl)
    g = gcompare(cx, f, '3', relow)
    Aa, V1, U = g['Aa'], g['Vv'], f['U']
    ra, rv = '( Re ` %s )' % Aa, '( Re ` %s )' % V1
    rar = D(w, A, 'recld', [g['ac']], '%s e. RR' % ra); rvr = D(w, A, 'recld', [g['vc']], '%s e. RR' % rv)
    cl = Closure(w, A, {'P': ('RR', pr), '( Re ` Z )': ('RR', rz), ra: ('RR', rar), rv: ('RR', rvr)})
    ea = D(w, A, 'eqled', [rar, g['rea']], '%s <_ %s' % (ra, RA)); ea2 = D(w, A, 'eqled', [D(w, A, 'readdcld', [D(w, A, 'remulcld', [cx.nhr, rz], '( %s x. ( Re ` Z ) ) e. RR' % NH),
                                                                                                               cx.rcoef('1')[1]], '%s e. RR' % RA),
                                                                                          w.s([g['rea']], 'eqcomd', '( %s -> %s = %s )' % (A, RA, ra))], '%s <_ %s' % (RA, ra))
    ev = D(w, A, 'eqled', [rvr, g['rev']], '%s <_ %s' % (rv, RV)); ev2 = D(w, A, 'eqled', [D(w, A, 'readdcld', [D(w, A, 'remulcld', [cx.hr, rz], '( %s x. ( Re ` Z ) ) e. RR' % HALF),
                                                                                                               cx.rcoef('3')[1]], '%s e. RR' % RV),
                                                                                          w.s([g['rev']], 'eqcomd', '( %s -> %s = %s )' % (A, RV, rv))], '%s <_ %s' % (RV, rv))
    hs = [ge, le, p0, p1]
    ain = in_i100(w, A, ra, rar, linarith(w, A, hs + [ea2], '( 1 / ; ; 1 0 0 ) <_ %s' % ra, closure=cl), linarith(w, A, hs + [ea], '%s <_ 3' % ra, closure=cl), cl)
    vin = in_i100(w, A, rv, rvr, linarith(w, A, hs + [ev2], '( 1 / ; ; 1 0 0 ) <_ %s' % rv, closure=cl), linarith(w, A, hs + [ev], '%s <_ 3' % rv, closure=cl), cl)
    idp = w.s([], 'id', '( p = %s -> p = %s )' % (ra, ra))
    s1, v1 = w.wcongr('( _G ` p ) <_ ( D x. ( _G ` q ) )', {'p': ra}, 'p = %s' % ra, {'p': idp})
    idq = w.s([], 'id', '( q = %s -> q = %s )' % (rv, rv))
    s2, v2 = w.wcongr(v1, {'q': rv}, 'q = %s' % rv, {'q': idq})
    rat = w.s([s1, s2, hall, ain, vin], 'rspc2dv', '( %s -> %s )' % (A, v2))
    GA, GV = '( abs ` ( _G ` %s ) )' % Aa, '( abs ` ( _G ` %s ) )' % V1
    GRa, GRv = '( _G ` %s )' % ra, '( _G ` %s )' % rv
    vpos = w.s([linarith(w, A, [ge, p0], '0 < %s' % RV, closure=cx.cl), g['rev']], 'breqtrrd', '( %s -> 0 < %s )' % (A, rv))
    gv = w.s([w.s([rvr, vpos], 'jca', '( %s -> ( %s e. RR /\\ 0 < %s ) )' % (A, rv, rv)), w.inst('gamrrp')], 'syl', '( %s -> %s e. RR+ )' % (A, GRv))
    gar = w.s([w.s([rar, g['pa']], 'jca', '( %s -> ( %s e. RR /\\ 0 < %s ) )' % (A, ra, ra)), w.inst('gamrrp')], 'syl', '( %s -> %s e. RR+ )' % (A, GRa))
    GAr = D(w, A, 'abscld', [f['g1c']], '%s e. RR' % GA); GVr = D(w, A, 'abscld', [f['g3c']], '%s e. RR' % GV)
    dr = D(w, A, 'rpred', [drp], 'D e. RR')
    m1 = D(w, A, 'lemul2ad', [D(w, A, 'rpred', [gar], '%s e. RR' % GRa), D(w, A, 'remulcld', [dr, D(w, A, 'rpred', [gv], '%s e. RR' % GRv)], '( D x. %s ) e. RR' % GRv),
                              GVr, D(w, A, 'absge0d', [f['g3c']], '0 <_ %s' % GV), rat], '( %s x. %s ) <_ ( %s x. ( D x. %s ) )' % (GV, GRa, GV, GRv))
    gvc = D(w, A, 'recnd', [GVr], '%s e. CC' % GV); dc = D(w, A, 'rpcnd', [drp], 'D e. CC'); grvc = D(w, A, 'rpcnd', [gv], '%s e. CC' % GRv)
    as1 = w.s([E(w, A, 'mulassd', [gvc, dc, grvc], '( ( %s x. D ) x. %s )' % (GV, GRv), '( %s x. ( D x. %s ) )' % (GV, GRv))], 'eqcomd',
              '( %s -> ( %s x. ( D x. %s ) ) = ( ( %s x. D ) x. %s ) )' % (A, GV, GRv, GV, GRv))
    m2 = D(w, A, 'letrd', [D(w, A, 'remulcld', [GAr, D(w, A, 'rpred', [gv], '%s e. RR' % GRv)], '( %s x. %s ) e. RR' % (GA, GRv)),
                           D(w, A, 'remulcld', [GVr, D(w, A, 'rpred', [gar], '%s e. RR' % GRa)], '( %s x. %s ) e. RR' % (GV, GRa)),
                           D(w, A, 'remulcld', [D(w, A, 'remulcld', [GVr, dr], '( %s x. D ) e. RR' % GV), D(w, A, 'rpred', [gv], '%s e. RR' % GRv)], '( ( %s x. D ) x. %s ) e. RR' % (GV, GRv)),
                           g['gm'], w.s([m1, as1], 'breqtrd', '( %s -> ( %s x. %s ) <_ ( ( %s x. D ) x. %s ) )' % (A, GV, GRa, GV, GRv))],
           '( %s x. %s ) <_ ( ( %s x. D ) x. %s )' % (GA, GRv, GV, GRv))
    gle = w.s([m2, D(w, A, 'lemul1d', [GAr, D(w, A, 'remulcld', [GVr, dr], '( %s x. D ) e. RR' % GV), gv],
                     '( %s <_ ( %s x. D ) <-> ( %s x. %s ) <_ ( ( %s x. D ) x. %s ) )' % (GA, GV, GA, GRv, GV, GRv))], 'mpbird', '( %s -> %s <_ ( %s x. D ) )' % (A, GA, GV))
    mod = modulus(cx, f)
    AU = '( abs ` %s )' % U
    aur = D(w, A, 'abscld', [f['uc']], '%s e. RR' % AU)
    gvrp = D(w, A, 'absrpcld', [f['g3c'], f['g3n']], '%s e. RR+' % GV)
    Q = '( %s / %s )' % (AU, GV)
    qr = D(w, A, 'rerpdivcld', [aur, gvrp], '%s e. RR' % Q)
    q0 = D(w, A, 'divge0d', [aur, gvrp, D(w, A, 'absge0d', [f['uc']], '0 <_ %s' % AU)], '0 <_ %s' % Q)
    m3 = D(w, A, 'lemul1ad', [GAr, D(w, A, 'remulcld', [GVr, dr], '( %s x. D ) e. RR' % GV), qr, q0, gle], '( %s x. %s ) <_ ( ( %s x. D ) x. %s )' % (GA, Q, GV, Q))
    # ( ( GV x. D ) x. Q ) = ( D x. AU )
    e1 = E(w, A, 'mul32d', [gvc, dc, D(w, A, 'recnd', [qr], '%s e. CC' % Q)], '( ( %s x. D ) x. %s )' % (GV, Q), '( ( %s x. %s ) x. D )' % (GV, Q))
    e2 = E(w, A, 'oveq1d', [E(w, A, 'divcan2d', [D(w, A, 'recnd', [aur], '%s e. CC' % AU), D(w, A, 'rpcnd', [gvrp], '%s e. CC' % GV), D(w, A, 'rpne0d', [gvrp], '%s =/= 0' % GV)],
                              '( %s x. %s )' % (GV, Q), AU)], '( ( %s x. %s ) x. D )' % (GV, Q), '( %s x. D )' % AU)
    m4 = w.s([m3, w.s([e1, e2], 'eqtrd', '( %s -> ( ( %s x. D ) x. %s ) = ( %s x. D ) )' % (A, GV, Q, AU))], 'breqtrd', '( %s -> ( %s x. %s ) <_ ( %s x. D ) )' % (A, GA, Q, AU))
    EX = '( ( Re ` Z ) - ( 1 / 2 ) )'
    exr = D(w, A, 'resubcld', [rz, cx.hr], '%s e. RR' % EX)
    exle = linarith(w, A, [le], '%s <_ 0' % EX, closure=cx.cl)
    one_pi = linarith(w, A, [w.s([w.s([], 'pigt3', '3 < _pi')], 'a1i', '( %s -> 3 < _pi )' % A)], '1 <_ _pi', closure=Closure(w, A, {'_pi': ('RR', a1(w, A, 'pire', '_pi e. RR'))}))
    pwle = w.s([w.s([a1(w, A, 'pire', '_pi e. RR'), one_pi], 'jca', '( %s -> ( _pi e. RR /\\ 1 <_ _pi ) )' % A),
                w.s([exr, a1(w, A, '0re', '0 e. RR')], 'jca', '( %s -> ( %s e. RR /\\ 0 e. RR ) )' % (A, EX)), exle, w.inst('cxplea')], 'syl3anc',
               '( %s -> ( _pi ^c %s ) <_ ( _pi ^c 0 ) )' % (A, EX))
    pw1 = w.s([pwle, w.s([w.s([w.s([], 'picn', '_pi e. CC'), w.inst('cxp0')], 'ax-mp', '( _pi ^c 0 ) = 1')], 'a1i', '( %s -> ( _pi ^c 0 ) = 1 )' % A)], 'breqtrd',
              '( %s -> ( _pi ^c %s ) <_ 1 )' % (A, EX))
    pwrp = D(w, A, 'rpcxpcld', [a1(w, A, 'pirp', '_pi e. RR+'), exr], '( _pi ^c %s ) e. RR+' % EX)
    Y = '( %s x. %s )' % (GA, Q)
    yr = D(w, A, 'remulcld', [GAr, qr], '%s e. RR' % Y)
    y0 = D(w, A, 'mulge0d', [GAr, qr, D(w, A, 'absge0d', [f['g1c']], '0 <_ %s' % GA), q0], '0 <_ %s' % Y)
    AUD = '( %s x. D )' % AU
    m5 = D(w, A, 'lemul12ad', [D(w, A, 'rpred', [pwrp], '( _pi ^c %s ) e. RR' % EX), a1(w, A, '1re', '1 e. RR'), yr, D(w, A, 'remulcld', [aur, dr], '%s e. RR' % AUD),
                               D(w, A, 'rpge0d', [pwrp], '0 <_ ( _pi ^c %s )' % EX), y0, pw1, m4], '( ( _pi ^c %s ) x. %s ) <_ ( 1 x. %s )' % (EX, Y, AUD))
    m6 = w.s([m5, E(w, A, 'mullidd', [D(w, A, 'recnd', [D(w, A, 'remulcld', [aur, dr], '%s e. RR' % AUD)], '%s e. CC' % AUD)], '( 1 x. %s )' % AUD, AUD)], 'breqtrd',
             '( %s -> ( ( _pi ^c %s ) x. %s ) <_ %s )' % (A, EX, Y, AUD))
    fin1 = w.s([mod, m6], 'eqbrtrd', '( %s -> ( abs ` ( %s ` Z ) ) <_ %s )' % (A, L.FL, AUD))
    au = absU(cx, f, ge, le, p1)
    # AU x. D <_ ( 2 D ) exp ( 1 x. | Im Z | )
    AIX = '( abs ` ( Im ` Z ) )'
    aix = D(w, A, 'abscld', [D(w, A, 'recnd', [D(w, A, 'imcld', [zc], '( Im ` Z ) e. RR')], '( Im ` Z ) e. CC')], '%s e. RR' % AIX)
    aix0 = D(w, A, 'absge0d', [D(w, A, 'recnd', [D(w, A, 'imcld', [zc], '( Im ` Z ) e. RR')], '( Im ` Z ) e. CC')], '0 <_ %s' % AIX)
    EXP = '( exp ` ( 1 x. %s ) )' % AIX
    e1x = E(w, A, 'fveq2d', [E(w, A, 'mullidd', [D(w, A, 'recnd', [aix], '%s e. CC' % AIX)], '( 1 x. %s )' % AIX, AIX)], EXP, '( exp ` %s )' % AIX)
    bv = w.s([w.s([aix, aix0], 'jca', '( %s -> ( %s e. RR /\\ 0 <_ %s ) )' % (A, AIX, AIX)), w.inst('bvefge1p')], 'syl', '( %s -> ( 1 + %s ) <_ ( exp ` %s ) )' % (A, AIX, AIX))
    bv2 = w.s([bv, e1x], 'breqtrrd', '( %s -> ( 1 + %s ) <_ %s )' % (A, AIX, EXP))
    expr = D(w, A, 'reefcld', [D(w, A, 'remulcld', [a1(w, A, '1re', '1 e. RR'), aix], '( 1 x. %s ) e. RR' % AIX)], '%s e. RR' % EXP)
    clf = Closure(w, A, {AIX: ('RR', aix), EXP: ('RR', expr), AU: ('RR', aur)})
    u2 = linarith(w, A, [au, bv2, aix0], '%s <_ ( 2 x. %s )' % (AU, EXP), closure=clf)
    m7 = D(w, A, 'lemul1ad', [aur, D(w, A, 'remulcld', [a1(w, A, '2re', '2 e. RR'), expr], '( 2 x. %s ) e. RR' % EXP), dr, D(w, A, 'rpge0d', [drp], '0 <_ D'), u2],
           '%s <_ ( ( 2 x. %s ) x. D )' % (AUD, EXP))
    e7 = w.s([E(w, A, 'mul32d', [a1(w, A, '2cn', '2 e. CC'), dc, D(w, A, 'recnd', [expr], '%s e. CC' % EXP)], '( ( 2 x. D ) x. %s )' % EXP, '( ( 2 x. %s ) x. D )' % EXP)],
             'eqcomd', '( %s -> ( ( 2 x. %s ) x. D ) = ( ( 2 x. D ) x. %s ) )' % (A, EXP, EXP))
    m8 = w.s([m7, e7], 'breqtrd', '( %s -> %s <_ ( ( 2 x. D ) x. %s ) )' % (A, AUD, EXP))
    flr = D(w, A, 'abscld', [w.s([f['fv'], f['flc']], 'eqeltrd', '( %s -> ( %s ` Z ) e. CC )' % (A, L.FL))], '( abs ` ( %s ` Z ) ) e. RR' % L.FL)
    w.qed([flr, D(w, A, 'remulcld', [aur, dr], '%s e. RR' % AUD), D(w, A, 'remulcld', [D(w, A, 'remulcld', [a1(w, A, '2re', '2 e. RR'), dr], '( 2 x. D ) e. RR'), expr],
                                                                            '( ( 2 x. D ) x. %s ) e. RR' % EXP), fin1, m8], 'letrd', L.STATEMENTS['zl3qgb'])
    go(w)


# ---------------------------------------------------------------- zl3qgr
if __name__ == '__main__' and want('zl3qgr'):
    w = W('zl3qgr', 'Growth of the symmetric Gamma ratio on the strip ` -1/2 <_ Re z <_ 1/2 ` : ` | QQ ( z ) | <_ k e ^ | Im z | ` '
          '( ~ zl3qgb with the constant of ~ zl3grat ).')
    A, Cc = ante_of('zl3qgr')
    I = L.I100
    HDd = 'A. p e. %s A. q e. %s ( _G ` p ) <_ ( d x. ( _G ` q ) )' % (I, I)
    Ad = '( %s /\\ ( d e. RR+ /\\ %s ) )' % (A, HDd)
    SQ = L.SQ
    Az = '( %s /\\ z e. %s )' % (Ad, SQ)
    BODY = lambda k: '( abs ` ( %s ` z ) ) <_ ( %s x. ( exp ` ( 1 x. ( abs ` ( Im ` z ) ) ) ) )' % (L.FL, k)
    zs = D(w, Az, 'simpr', [], 'z e. %s' % SQ)
    el = w.s([zs, w.s([], 'elstr', '( z e. %s <-> ( z e. CC /\\ ( Re ` z ) e. ( -u ( 1 / 2 ) [,] ( 1 / 2 ) ) ) )' % SQ)], 'sylib',
             '( %s -> ( z e. CC /\\ ( Re ` z ) e. ( -u ( 1 / 2 ) [,] ( 1 / 2 ) ) ) )' % Az)
    zc = D(w, Az, 'simpld', [el], 'z e. CC')
    ri = D(w, Az, 'simprd', [el], '( Re ` z ) e. ( -u ( 1 / 2 ) [,] ( 1 / 2 ) )')
    nh = D(w, Az, 'renegcld', [a1(w, Az, 'halfre', '( 1 / 2 ) e. RR')], '-u ( 1 / 2 ) e. RR')
    bi = w.s([nh, a1(w, Az, 'halfre', '( 1 / 2 ) e. RR'), w.inst('elicc2')], 'syl2anc',
             '( %s -> ( ( Re ` z ) e. ( -u ( 1 / 2 ) [,] ( 1 / 2 ) ) <-> ( ( Re ` z ) e. RR /\\ -u ( 1 / 2 ) <_ ( Re ` z ) /\\ ( Re ` z ) <_ ( 1 / 2 ) ) ) )' % Az)
    r3 = w.s([ri, bi], 'mpbid', '( %s -> ( ( Re ` z ) e. RR /\\ -u ( 1 / 2 ) <_ ( Re ` z ) /\\ ( Re ` z ) <_ ( 1 / 2 ) ) )' % Az)
    zh = w.s([zc, D(w, Az, 'simp2d', [r3], '-u ( 1 / 2 ) <_ ( Re ` z )'), D(w, Az, 'simp3d', [r3], '( Re ` z ) <_ ( 1 / 2 )')], '3jca',
             '( %s -> ( z e. CC /\\ -u ( 1 / 2 ) <_ ( Re ` z ) /\\ ( Re ` z ) <_ ( 1 / 2 ) ) )' % Az)
    gb = w.s([w.s([D(w, Az, 'simpl', [], Ad), zh], 'jca', '( %s -> ( %s /\\ ( z e. CC /\\ -u ( 1 / 2 ) <_ ( Re ` z ) /\\ ( Re ` z ) <_ ( 1 / 2 ) ) ) )' % (Az, Ad)),
              w.inst('zl3qgb')], 'syl', '( %s -> %s )' % (Az, BODY('( 2 x. d )')))
    allz = w.s([gb], 'ralrimiva', '( %s -> A. z e. %s %s )' % (Ad, SQ, BODY('( 2 x. d )')))
    k2 = D(w, Ad, 'rpmulcld', [a1(w, Ad, '2rp', '2 e. RR+'), D(w, Ad, 'simprl', [], 'd e. RR+')], '( 2 x. d ) e. RR+')
    idk = w.s([], 'id', '( k = ( 2 x. d ) -> k = ( 2 x. d ) )')
    sk, vk = w.wcongr('A. z e. %s %s' % (SQ, BODY('k')), {'k': '( 2 x. d )'}, 'k = ( 2 x. d )', {'k': idk})
    skd = w.s([sk], 'adantl', '( ( %s /\\ k = ( 2 x. d ) ) -> ( A. z e. %s %s <-> %s ) )' % (Ad, SQ, BODY('k'), vk))
    ex = w.s([k2, skd, allz], 'rspcedvd', '( %s -> %s )' % (Ad, Cc))
    lim = w.s([ex], 'rexlimdvaa', '( %s -> ( E. d e. RR+ %s -> %s ) )' % (A, HDd, Cc))
    w.qed([w.s([w.s([], 'zl3grat', 'E. d e. RR+ %s' % HDd)], 'a1i', '( %s -> E. d e. RR+ %s )' % (A, HDd)), lim], 'mpd', L.STATEMENTS['zl3qgr'])
    go(w)


def gauss3y(w, A, Eb, er, wr, iyr, iwr, sqle, y='y'):
    """( A -> ( exp ` ( ( ( Eb - ( Re ` W ) ) ^ 2 ) - ( V ^ 2 ) ) ) <_ ( 3 x. ( exp ` -u ( V ^ 2 ) ) ) ), V = ( ( Im ` y ) - ( Im ` W ) )"""
    from zl2lib import e1le3
    a = '( ( %s - ( Re ` W ) ) ^ 2 )' % Eb
    V = '( ( Im ` %s ) - ( Im ` W ) )' % y
    b = '( %s ^ 2 )' % V
    ar = D(w, A, 'resqcld', [D(w, A, 'resubcld', [er, wr], '( %s - ( Re ` W ) ) e. RR' % Eb)], '%s e. RR' % a)
    vr = D(w, A, 'resubcld', [iyr, iwr], '%s e. RR' % V)
    br = D(w, A, 'resqcld', [vr], '%s e. RR' % b)
    ac = D(w, A, 'recnd', [ar], '%s e. CC' % a); bc = D(w, A, 'recnd', [br], '%s e. CC' % b)
    e1 = w.s([w.s([ac, bc], 'negsubd', '( %s -> ( %s + -u %s ) = ( %s - %s ) )' % (A, a, b, a, b))], 'eqcomd', '( %s -> ( %s - %s ) = ( %s + -u %s ) )' % (A, a, b, a, b))
    e2 = E(w, A, 'fveq2d', [e1], '( exp ` ( %s - %s ) )' % (a, b), '( exp ` ( %s + -u %s ) )' % (a, b))
    e3 = efadd_(w, A, a, '-u %s' % b, ac, D(w, A, 'negcld', [bc], '-u %s e. CC' % b))
    eq = w.s([e2, e3], 'eqtrd', '( %s -> ( exp ` ( %s - %s ) ) = ( ( exp ` %s ) x. ( exp ` -u %s ) ) )' % (A, a, b, a, b))
    one = a1(w, A, '1re', '1 e. RR')
    le1 = efle_(w, A, a, '1', ar, one, sqle)
    e13 = w.s([e1le3(w)], 'a1i', '( %s -> ( exp ` 1 ) <_ 3 )' % A)
    ea = D(w, A, 'reefcld', [ar], '( exp ` %s ) e. RR' % a)
    le3 = D(w, A, 'letrd', [ea, D(w, A, 'reefcld', [one], '( exp ` 1 ) e. RR'), a1(w, A, '3re', '3 e. RR'), le1, e13], '( exp ` %s ) <_ 3' % a)
    nb = D(w, A, 'renegcld', [br], '-u %s e. RR' % b)
    enb = D(w, A, 'reefcld', [nb], '( exp ` -u %s ) e. RR' % b)
    enb0 = D(w, A, 'ltled', [a1(w, A, '0re', '0 e. RR'), enb, w.s([nb, w.inst('efgt0')], 'syl', '( %s -> 0 < ( exp ` -u %s ) )' % (A, b))], '0 <_ ( exp ` -u %s )' % b)
    m = D(w, A, 'lemul1ad', [ea, a1(w, A, '3re', '3 e. RR'), enb, enb0, le3], '( ( exp ` %s ) x. ( exp ` -u %s ) ) <_ ( 3 x. ( exp ` -u %s ) )' % (a, b, b))
    return w.s([eq, m], 'eqbrtrd', '( %s -> ( exp ` ( %s - %s ) ) <_ ( 3 x. ( exp ` -u %s ) ) )' % (A, a, b, b)), enb, enb0, vr, br


# ---------------------------------------------------------------- zl3gint
if __name__ == '__main__' and want('zl3gint'):
    w = W('zl3gint', 'Interpolation on the strip ` -1/2 <_ Re z <_ 1/2 ` : a holomorphic function of exponential type bounded by ` | Im z | + 2 ` '
          'on ` Re z = -1/2 ` and by ` 1 ` on ` Re z = 1/2 ` is bounded by ` 9 ( | Im W | + 2 ) ^ ( 1/2 - Re W ) ` inside '
          '( ~ zl2pln with ` P = 1/2 ` , ` C = log ( | Im W | + 2 ) ` ; model ~ zl2gint ).')
    A, Cc = ante_of('zl3gint')
    S = L.SQ
    X, Y = NH, HALF
    GR = L.GRW('F', S)
    EL = 'A. z e. CC ( ( Re ` z ) = -u ( 1 / 2 ) -> ( abs ` ( F ` z ) ) <_ ( ( abs ` ( Im ` z ) ) + 2 ) )'
    ER = 'A. z e. CC ( ( Re ` z ) = ( 1 / 2 ) -> ( abs ` ( F ` z ) ) <_ 1 )'
    HOL3 = '( F e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D F ) /\\ %s C_ D )' % S
    h3 = D(w, A, 'simpll', [], '( %s /\\ %s )' % (HOL3, GR))
    hol3 = D(w, A, 'simpld', [h3], HOL3); gr = D(w, A, 'simprd', [h3], GR)
    edges = D(w, A, 'simplr', [], '( %s /\\ %s )' % (EL, ER))
    el = D(w, A, 'simpld', [edges], EL); er_ = D(w, A, 'simprd', [edges], ER)
    wc = D(w, A, 'simprl', [], 'W e. CC')
    wlr = D(w, A, 'simprr', [], '( -u ( 1 / 2 ) <_ ( Re ` W ) /\\ ( Re ` W ) <_ ( 1 / 2 ) )')
    w1 = D(w, A, 'simpld', [wlr], '-u ( 1 / 2 ) <_ ( Re ` W )'); w2 = D(w, A, 'simprd', [wlr], '( Re ` W ) <_ ( 1 / 2 )')
    wr = D(w, A, 'recld', [wc], '( Re ` W ) e. RR'); iwr = D(w, A, 'imcld', [wc], '( Im ` W ) e. RR')
    hr = a1(w, A, 'halfre', '( 1 / 2 ) e. RR'); nhr = D(w, A, 'renegcld', [hr], '-u ( 1 / 2 ) e. RR')
    ic2 = w.s([nhr, hr, w.inst('elicc2')], 'syl2anc', '( %s -> ( ( Re ` W ) e. ( -u ( 1 / 2 ) [,] ( 1 / 2 ) ) <-> ( ( Re ` W ) e. RR /\\ -u ( 1 / 2 ) <_ ( Re ` W ) /\\ ( Re ` W ) <_ ( 1 / 2 ) ) ) )' % A)
    ric = w.s([w.s([wr, w1, w2], '3jca', '( %s -> ( ( Re ` W ) e. RR /\\ -u ( 1 / 2 ) <_ ( Re ` W ) /\\ ( Re ` W ) <_ ( 1 / 2 ) ) )' % A), ic2], 'mpbird',
              '( %s -> ( Re ` W ) e. ( -u ( 1 / 2 ) [,] ( 1 / 2 ) ) )' % A)
    wS = w.s([w.s([wc, ric], 'jca', '( %s -> ( W e. CC /\\ ( Re ` W ) e. ( -u ( 1 / 2 ) [,] ( 1 / 2 ) ) ) )' % A),
              w.s([], 'elstr', '( W e. %s <-> ( W e. CC /\\ ( Re ` W ) e. ( -u ( 1 / 2 ) [,] ( 1 / 2 ) ) ) )' % S)], 'sylibr', '( %s -> W e. %s )' % (A, S))
    Qd = '( ( abs ` ( Im ` W ) ) + 2 )'
    aiw = D(w, A, 'abscld', [D(w, A, 'recnd', [iwr], '( Im ` W ) e. CC')], '( abs ` ( Im ` W ) ) e. RR')
    aiw0 = D(w, A, 'absge0d', [D(w, A, 'recnd', [iwr], '( Im ` W ) e. CC')], '0 <_ ( abs ` ( Im ` W ) )')
    qr = D(w, A, 'readdcld', [aiw, a1(w, A, '2re', '2 e. RR')], '%s e. RR' % Qd)
    qp = linarith(w, A, [aiw0], '0 < %s' % Qd, closure=Closure(w, A, {'( abs ` ( Im ` W ) )': ('RR', aiw)}))
    qrp = D(w, A, 'elrpd', [qr, qp], '%s e. RR+' % Qd)
    LQ = '( log ` %s )' % Qd
    lqr = D(w, A, 'relogcld', [qrp], '%s e. RR' % LQ)
    # context y e. S
    Ay = '( %s /\\ y e. %s )' % (A, S)
    ys = D(w, Ay, 'simpr', [], 'y e. %s' % S)
    yel = w.s([ys, w.s([], 'elstr', '( y e. %s <-> ( y e. CC /\\ ( Re ` y ) e. ( -u ( 1 / 2 ) [,] ( 1 / 2 ) ) ) )' % S)], 'sylib',
              '( %s -> ( y e. CC /\\ ( Re ` y ) e. ( -u ( 1 / 2 ) [,] ( 1 / 2 ) ) ) )' % Ay)
    yc = D(w, Ay, 'simpld', [yel], 'y e. CC')
    iyr = D(w, Ay, 'imcld', [yc], '( Im ` y ) e. RR')
    La = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (Ay, f))
    fcn = D(w, A, 'simp1d', [hol3], 'F e. ( D -cn-> CC )'); sd = D(w, A, 'simp3d', [hol3], '%s C_ D' % S)
    ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A)
    fyc = w.s([La(ff, 'F : D --> CC'), w.s([La(sd, '%s C_ D' % S), ys], 'sseldd', '( %s -> y e. D )' % Ay)], 'ffvelcdmd', '( %s -> ( F ` y ) e. CC )' % Ay)
    afy = D(w, Ay, 'abscld', [fyc], '( abs ` ( F ` y ) ) e. RR'); afy0 = D(w, Ay, 'absge0d', [fyc], '0 <_ ( abs ` ( F ` y ) )')
    wry, iwry = La(wr, '( Re ` W ) e. RR'), La(iwr, '( Im ` W ) e. RR')
    V = '( ( Im ` y ) - ( Im ` W ) )'
    DV = '( abs ` %s )' % V
    H = '( exp ` -u ( %s ^ 2 ) )' % V

    def edge(Xe, other):
        """( Ay -> ( ( Re ` y ) = Xe -> normalized <_ 9 ) )"""
        Ae = '( %s /\\ ( Re ` y ) = %s )' % (Ay, Xe)
        Le = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (Ae, f))
        xr = Le(La(nhr if Xe == NH else hr, '%s e. RR' % Xe), '%s e. RR' % Xe)
        wre = Le(wry, '( Re ` W ) e. RR')
        cl = Closure(w, Ae, {'( Re ` W )': ('RR', wre)})
        w1e = Le(La(w1, '-u ( 1 / 2 ) <_ ( Re ` W )'), '-u ( 1 / 2 ) <_ ( Re ` W )'); w2e = Le(La(w2, '( Re ` W ) <_ ( 1 / 2 )'), '( Re ` W ) <_ ( 1 / 2 )')
        sqle = nlinarith(w, Ae, [w1e, w2e], '( ( %s - ( Re ` W ) ) ^ 2 ) <_ 1' % Xe, closure=cl)
        g, enb, enb0, vr, br = gauss3y(w, Ae, Xe, xr, wre, Le(iyr, '( Im ` y ) e. RR'), Le(iwry, '( Im ` W ) e. RR'), sqle)
        GX = '( exp ` ( ( ( %s - ( Re ` W ) ) ^ 2 ) - ( %s ^ 2 ) ) )' % (Xe, V)
        gxr = D(w, Ae, 'reefcld', [D(w, Ae, 'resubcld', [D(w, Ae, 'resqcld', [D(w, Ae, 'resubcld', [xr, wre], '( %s - ( Re ` W ) ) e. RR' % Xe)], '( ( %s - ( Re ` W ) ) ^ 2 ) e. RR' % Xe), br],
                                                  '( ( ( %s - ( Re ` W ) ) ^ 2 ) - ( %s ^ 2 ) ) e. RR' % (Xe, V))], '%s e. RR' % GX)
        gx0 = D(w, Ae, 'ltled', [a1(w, Ae, '0re', '0 e. RR'), gxr, D(w, Ae, 'efgt0d' if False else 'rpgt0d', [D(w, Ae, 'rpefcld' if False else 'idi', [], 'x')], 'x') if False else
                                 w.s([D(w, Ae, 'resubcld', [D(w, Ae, 'resqcld', [D(w, Ae, 'resubcld', [xr, wre], '( %s - ( Re ` W ) ) e. RR' % Xe)], '( ( %s - ( Re ` W ) ) ^ 2 ) e. RR' % Xe), br],
                                                 '( ( ( %s - ( Re ` W ) ) ^ 2 ) - ( %s ^ 2 ) ) e. RR' % (Xe, V)), w.inst('efgt0')], 'syl', '( %s -> 0 < %s )' % (Ae, GX))], '0 <_ %s' % GX)
        EXX = '( exp ` ( ( %s - ( 1 / 2 ) ) x. %s ) )' % (Xe, LQ)
        # the edge bound on F
        ye = w.s([Le(yc, 'y e. CC'), w.s([w.s([w.s([], 'fveqeq2', '( z = y -> ( ( Re ` z ) = %s <-> ( Re ` y ) = %s ) )' % (Xe, Xe)) if False else
                                          w.s([w.s([], 'fveq2', '( z = y -> ( Re ` z ) = ( Re ` y ) )')], 'eqeq1d', '( z = y -> ( ( Re ` z ) = %s <-> ( Re ` y ) = %s ) )' % (Xe, Xe)),
                                          w.s([w.s([w.s([], 'fveq2', '( z = y -> ( F ` z ) = ( F ` y ) )')], 'fveq2d', '( z = y -> ( abs ` ( F ` z ) ) = ( abs ` ( F ` y ) ) )'),
                                               (w.s([w.s([w.s([w.s([], 'fveq2', '( z = y -> ( Im ` z ) = ( Im ` y ) )')], 'fveq2d', '( z = y -> ( abs ` ( Im ` z ) ) = ( abs ` ( Im ` y ) ) )')],
                                                          'oveq1d', '( z = y -> ( ( abs ` ( Im ` z ) ) + 2 ) = ( ( abs ` ( Im ` y ) ) + 2 ) )')], 'idi',
                                                     '( z = y -> ( ( abs ` ( Im ` z ) ) + 2 ) = ( ( abs ` ( Im ` y ) ) + 2 ) )') if Xe == NH else
                                                w.s([], 'eqidd', '( z = y -> 1 = 1 )'))],
                                              'breq12d', '( z = y -> ( ( abs ` ( F ` z ) ) <_ %s <-> ( abs ` ( F ` y ) ) <_ %s ) )' % (
                                                  '( ( abs ` ( Im ` z ) ) + 2 )' if Xe == NH else '1', '( ( abs ` ( Im ` y ) ) + 2 )' if Xe == NH else '1'))],
                                         'imbi12d', '( z = y -> ( ( ( Re ` z ) = %s -> ( abs ` ( F ` z ) ) <_ %s ) <-> ( ( Re ` y ) = %s -> ( abs ` ( F ` y ) ) <_ %s ) ) )' % (
                                             Xe, '( ( abs ` ( Im ` z ) ) + 2 )' if Xe == NH else '1', Xe, '( ( abs ` ( Im ` y ) ) + 2 )' if Xe == NH else '1')),
                                    w.inst('rspcv')], 'syl', 'x') if False else None], 'idi', 'x') if False else None
        BZ = '( ( abs ` ( Im ` z ) ) + 2 )' if Xe == NH else '1'
        BY = '( ( abs ` ( Im ` y ) ) + 2 )' if Xe == NH else '1'
        c1 = w.s([w.s([], 'fveq2', '( z = y -> ( Re ` z ) = ( Re ` y ) )')], 'eqeq1d', '( z = y -> ( ( Re ` z ) = %s <-> ( Re ` y ) = %s ) )' % (Xe, Xe))
        c2 = w.s([w.s([], 'fveq2', '( z = y -> ( F ` z ) = ( F ` y ) )')], 'fveq2d', '( z = y -> ( abs ` ( F ` z ) ) = ( abs ` ( F ` y ) ) )')
        if Xe == NH:
            c3 = w.s([w.s([w.s([], 'fveq2', '( z = y -> ( Im ` z ) = ( Im ` y ) )')], 'fveq2d', '( z = y -> ( abs ` ( Im ` z ) ) = ( abs ` ( Im ` y ) ) )')],
                     'oveq1d', '( z = y -> %s = %s )' % (BZ, BY))
        else:
            c3 = w.s([], 'eqidd', '( z = y -> 1 = 1 )')
        c4 = w.s([c2, c3], 'breq12d', '( z = y -> ( ( abs ` ( F ` z ) ) <_ %s <-> ( abs ` ( F ` y ) ) <_ %s ) )' % (BZ, BY))
        c5 = w.s([c1, c4], 'imbi12d', '( z = y -> ( ( ( Re ` z ) = %s -> ( abs ` ( F ` z ) ) <_ %s ) <-> ( ( Re ` y ) = %s -> ( abs ` ( F ` y ) ) <_ %s ) ) )' % (Xe, BZ, Xe, BY))
        rs = w.s([c5], 'rspcv', '( y e. CC -> ( A. z e. CC ( ( Re ` z ) = %s -> ( abs ` ( F ` z ) ) <_ %s ) -> ( ( Re ` y ) = %s -> ( abs ` ( F ` y ) ) <_ %s ) ) )' % (Xe, BZ, Xe, BY))
        hyp_ = Le(La(el if Xe == NH else er_, EL if Xe == NH else ER), EL if Xe == NH else ER)
        fb = w.s([Le(yc, 'y e. CC'), hyp_, rs], 'sylc', '( %s -> ( ( Re ` y ) = %s -> ( abs ` ( F ` y ) ) <_ %s ) )' % (Ae, Xe, BY))
        fb = w.s([D(w, Ae, 'simpr', [], '( Re ` y ) = %s' % Xe), fb], 'mpd', '( %s -> ( abs ` ( F ` y ) ) <_ %s )' % (Ae, BY))
        afe = Le(afy, '( abs ` ( F ` y ) ) e. RR')
        if Xe == NH:
            # e ^ ( ( -1/2 - 1/2 ) log q ) = 1 / q
            lqe = Le(La(lqr, '%s e. RR' % LQ), '%s e. RR' % LQ)
            from lin import lineq
            hc_ = a1(w, Ae, 'halfcn', '( 1 / 2 ) e. CC'); lqc = D(w, Ae, 'recnd', [lqe], '%s e. CC' % LQ)
            n1 = w.s([w.s([hc_, hc_, w.inst('negdi2')], 'syl2anc', '( %s -> -u ( ( 1 / 2 ) + ( 1 / 2 ) ) = ( -u ( 1 / 2 ) - ( 1 / 2 ) ) )' % Ae),
                      E(w, Ae, 'negeqd', [w.s([w.s([w.s([], 'ax-1cn', '1 e. CC'), w.inst('2halves')], 'ax-mp', '( ( 1 / 2 ) + ( 1 / 2 ) ) = 1')], 'a1i',
                                              '( %s -> ( ( 1 / 2 ) + ( 1 / 2 ) ) = 1 )' % Ae)], '-u ( ( 1 / 2 ) + ( 1 / 2 ) )', '-u 1')], 'eqtr3d',
                     '( %s -> ( -u ( 1 / 2 ) - ( 1 / 2 ) ) = -u 1 )' % Ae)
            ex1 = chain(w, Ae, ['( ( %s - ( 1 / 2 ) ) x. %s )' % (Xe, LQ), '( -u 1 x. %s )' % LQ, '-u ( 1 x. %s )' % LQ, '-u %s' % LQ],
                        [E(w, Ae, 'oveq1d', [n1], '( ( %s - ( 1 / 2 ) ) x. %s )' % (Xe, LQ), '( -u 1 x. %s )' % LQ),
                         E(w, Ae, 'mulneg1d', [a1(w, Ae, 'ax-1cn', '1 e. CC'), lqc], '( -u 1 x. %s )' % LQ, '-u ( 1 x. %s )' % LQ),
                         E(w, Ae, 'negeqd', [E(w, Ae, 'mullidd', [lqc], '( 1 x. %s )' % LQ, LQ)], '-u ( 1 x. %s )' % LQ, '-u %s' % LQ)])
            qe = Le(La(qrp, '%s e. RR+' % Qd), '%s e. RR+' % Qd)
            ex2 = chain(w, Ae, [EXX, '( exp ` -u %s )' % LQ, '( 1 / ( exp ` %s ) )' % LQ, '( 1 / %s )' % Qd],
                        [E(w, Ae, 'fveq2d', [ex1], EXX, '( exp ` -u %s )' % LQ),
                         w.s([D(w, Ae, 'recnd', [lqe], '%s e. CC' % LQ), w.inst('efneg')], 'syl', '( %s -> ( exp ` -u %s ) = ( 1 / ( exp ` %s ) ) )' % (Ae, LQ, LQ)),
                         E(w, Ae, 'oveq2d', [w.s([qe, w.inst('reeflog')], 'syl', '( %s -> ( exp ` %s ) = %s )' % (Ae, LQ, Qd))], '( 1 / ( exp ` %s ) )' % LQ, '( 1 / %s )' % Qd)])
            # | F | <_ Qd ( 1 + |V| )
            tab = w.s([Le(iyr, '( Im ` y ) e. RR'), Le(iwry, '( Im ` W ) e. RR'), w.inst('zl2tab')], 'syl2anc', '( %s -> ( ( abs ` ( Im ` y ) ) + 2 ) <_ ( %s x. ( 1 + %s ) ) )' % (Ae, Qd, DV))
            dvr = D(w, Ae, 'abscld', [D(w, Ae, 'recnd', [vr], '%s e. CC' % V)], '%s e. RR' % DV)
            T1 = '( 1 + %s )' % DV
            t1r = D(w, Ae, 'readdcld', [a1(w, Ae, '1re', '1 e. RR'), dvr], '%s e. RR' % T1)
            fT = D(w, Ae, 'letrd', [afe, D(w, Ae, 'readdcld', [D(w, Ae, 'abscld', [D(w, Ae, 'recnd', [Le(iyr, '( Im ` y ) e. RR')], '( Im ` y ) e. CC')], '( abs ` ( Im ` y ) ) e. RR'),
                                                           a1(w, Ae, '2re', '2 e. RR')], '( ( abs ` ( Im ` y ) ) + 2 ) e. RR'),
                                    D(w, Ae, 'remulcld', [D(w, Ae, 'rpred', [qe], '%s e. RR' % Qd), t1r], '( %s x. %s ) e. RR' % (Qd, T1)), fb, tab],
                   '( abs ` ( F ` y ) ) <_ ( %s x. %s )' % (Qd, T1))
            fq = w.s([fT, D(w, Ae, 'ledivmuld', [afe, t1r, qe], '( ( ( abs ` ( F ` y ) ) / %s ) <_ %s <-> ( abs ` ( F ` y ) ) <_ ( %s x. %s ) )' % (Qd, T1, Qd, T1))],
                     'mpbird', '( %s -> ( ( abs ` ( F ` y ) ) / %s ) <_ %s )' % (Ae, Qd, T1))
            dr_ = E(w, Ae, 'divrecd', [D(w, Ae, 'recnd', [afe], '( abs ` ( F ` y ) ) e. CC'), D(w, Ae, 'rpcnd', [qe], '%s e. CC' % Qd), D(w, Ae, 'rpne0d', [qe], '%s =/= 0' % Qd)],
                    '( ( abs ` ( F ` y ) ) / %s )' % Qd, '( ( abs ` ( F ` y ) ) x. ( 1 / %s ) )' % Qd)
            # ( |F| x. EXX ) <_ T1
            fe = w.s([w.s([w.s([ex2], 'oveq2d', '( %s -> ( ( abs ` ( F ` y ) ) x. %s ) = ( ( abs ` ( F ` y ) ) x. ( 1 / %s ) ) )' % (Ae, EXX, Qd)), dr_], 'eqtr4d',
                          '( %s -> ( ( abs ` ( F ` y ) ) x. %s ) = ( ( abs ` ( F ` y ) ) / %s ) )' % (Ae, EXX, Qd)), fq], 'eqbrtrd',
                     '( %s -> ( ( abs ` ( F ` y ) ) x. %s ) <_ %s )' % (Ae, EXX, T1))
            BF = T1
        else:
            ex1 = E(w, Ae, 'fveq2d', [w.s([E(w, Ae, 'oveq1d', [E(w, Ae, 'subidd', [a1(w, Ae, 'halfcn', '( 1 / 2 ) e. CC')], '( ( 1 / 2 ) - ( 1 / 2 ) )', '0')],
                                              '( ( ( 1 / 2 ) - ( 1 / 2 ) ) x. %s )' % LQ, '( 0 x. %s )' % LQ),
                                           E(w, Ae, 'mul02d', [D(w, Ae, 'recnd', [Le(La(lqr, '%s e. RR' % LQ), '%s e. RR' % LQ)], '%s e. CC' % LQ)], '( 0 x. %s )' % LQ, '0')], 'eqtrd',
                                          '( %s -> ( ( ( 1 / 2 ) - ( 1 / 2 ) ) x. %s ) = 0 )' % (Ae, LQ))], EXX, '( exp ` 0 )')
            ex2 = w.s([ex1, w.s([w.s([], 'ef0', '( exp ` 0 ) = 1')], 'a1i', '( %s -> ( exp ` 0 ) = 1 )' % Ae)], 'eqtrd', '( %s -> %s = 1 )' % (Ae, EXX))
            fe = w.s([w.s([E(w, Ae, 'oveq2d', [ex2], '( ( abs ` ( F ` y ) ) x. %s )' % EXX, '( ( abs ` ( F ` y ) ) x. 1 )'),
                           E(w, Ae, 'mulridd', [D(w, Ae, 'recnd', [afe], '( abs ` ( F ` y ) ) e. CC')], '( ( abs ` ( F ` y ) ) x. 1 )', '( abs ` ( F ` y ) )')], 'eqtrd',
                          '( %s -> ( ( abs ` ( F ` y ) ) x. %s ) = ( abs ` ( F ` y ) ) )' % (Ae, EXX)), fb], 'eqbrtrd', '( %s -> ( ( abs ` ( F ` y ) ) x. %s ) <_ 1 )' % (Ae, EXX))
            BF = '1'
        # ( ( |F| x. GX ) x. EXX ) = ( ( |F| x. EXX ) x. GX ) <_ BF x. ( 3 H ) <_ 9
        exr = D(w, Ae, 'reefcld', [D(w, Ae, 'remulcld', [D(w, Ae, 'resubcld', [xr, a1(w, Ae, 'halfre', '( 1 / 2 ) e. RR')], '( %s - ( 1 / 2 ) ) e. RR' % Xe),
                                                         Le(La(lqr, '%s e. RR' % LQ), '%s e. RR' % LQ)], '( ( %s - ( 1 / 2 ) ) x. %s ) e. RR' % (Xe, LQ))], '%s e. RR' % EXX)
        ex0 = D(w, Ae, 'ltled', [a1(w, Ae, '0re', '0 e. RR'), exr, w.s([D(w, Ae, 'remulcld', [D(w, Ae, 'resubcld', [xr, a1(w, Ae, 'halfre', '( 1 / 2 ) e. RR')], '( %s - ( 1 / 2 ) ) e. RR' % Xe),
                                                                                        Le(La(lqr, '%s e. RR' % LQ), '%s e. RR' % LQ)], '( ( %s - ( 1 / 2 ) ) x. %s ) e. RR' % (Xe, LQ)),
                                                                        w.inst('efgt0')], 'syl', '( %s -> 0 < %s )' % (Ae, EXX))], '0 <_ %s' % EXX)
        NORM = '( ( ( abs ` ( F ` y ) ) x. %s ) x. %s )' % (GX, EXX)
        m32 = E(w, Ae, 'mul32d', [D(w, Ae, 'recnd', [afe], '( abs ` ( F ` y ) ) e. CC'), D(w, Ae, 'recnd', [gxr], '%s e. CC' % GX), D(w, Ae, 'recnd', [exr], '%s e. CC' % EXX)],
                NORM, '( ( ( abs ` ( F ` y ) ) x. %s ) x. %s )' % (EXX, GX))
        fe0 = D(w, Ae, 'mulge0d', [afe, exr, Le(afy0, '0 <_ ( abs ` ( F ` y ) )'), ex0], '0 <_ ( ( abs ` ( F ` y ) ) x. %s )' % EXX)
        bfr = (D(w, Ae, 'readdcld', [a1(w, Ae, '1re', '1 e. RR'), D(w, Ae, 'abscld', [D(w, Ae, 'recnd', [vr], '%s e. CC' % V)], '%s e. RR' % DV)], '%s e. RR' % BF)
               if Xe == NH else a1(w, Ae, '1re', '1 e. RR'))
        H3 = '( 3 x. %s )' % H
        mm = D(w, Ae, 'lemul12ad', [D(w, Ae, 'remulcld', [afe, exr], '( ( abs ` ( F ` y ) ) x. %s ) e. RR' % EXX), bfr, gxr,
                                    D(w, Ae, 'remulcld', [a1(w, Ae, '3re', '3 e. RR'), enb], '%s e. RR' % H3), fe0, gx0, fe, g],
               '( ( ( abs ` ( F ` y ) ) x. %s ) x. %s ) <_ ( %s x. %s )' % (EXX, GX, BF, H3))
        dvr2 = D(w, Ae, 'abscld', [D(w, Ae, 'recnd', [vr], '%s e. CC' % V)], '%s e. RR' % DV)
        clf = Closure(w, Ae, {DV: ('RR', dvr2), H: ('RR', enb)})
        if Xe == NH:
            gau = w.s([vr, w.inst('zl2gau')], 'syl', '( %s -> ( ( 1 + %s ) x. %s ) <_ 3 )' % (Ae, DV, H))
            last = nlinarith(w, Ae, [gau, enb0], '( %s x. %s ) <_ 9' % (BF, H3), closure=clf)
        else:
            nb0 = linarith(w, Ae, [], '-u ( %s ^ 2 ) <_ 0' % V, closure=Closure(w, Ae, {V: ('RR', vr)}), products=True) if False else None
            sq0 = D(w, Ae, 'sqge0d', [vr], '0 <_ ( %s ^ 2 )' % V)
            nb0 = D(w, Ae, 'le0neg2d' if False else 'idi', [], 'x') if False else linarith(w, Ae, [sq0], '-u ( %s ^ 2 ) <_ 0' % V, closure=Closure(w, Ae, {'( %s ^ 2 )' % V: ('RR', br)}))
            hle = w.s([efle_(w, Ae, '-u ( %s ^ 2 )' % V, '0', D(w, Ae, 'renegcld', [br], '-u ( %s ^ 2 ) e. RR' % V), a1(w, Ae, '0re', '0 e. RR'), nb0),
                       w.s([w.s([], 'ef0', '( exp ` 0 ) = 1')], 'a1i', '( %s -> ( exp ` 0 ) = 1 )' % Ae)], 'breqtrd', '( %s -> %s <_ 1 )' % (Ae, H))
            last = nlinarith(w, Ae, [hle, enb0], '( %s x. %s ) <_ 9' % (BF, H3), closure=clf)
        fin = D(w, Ae, 'letrd', [D(w, Ae, 'remulcld', [D(w, Ae, 'remulcld', [afe, exr], '( ( abs ` ( F ` y ) ) x. %s ) e. RR' % EXX), gxr],
                                           '( ( ( abs ` ( F ` y ) ) x. %s ) x. %s ) e. RR' % (EXX, GX)),
                                 D(w, Ae, 'remulcld', [bfr, D(w, Ae, 'remulcld', [a1(w, Ae, '3re', '3 e. RR'), enb], '%s e. RR' % H3)], '( %s x. %s ) e. RR' % (BF, H3)),
                                 a1(w, Ae, '9re', '9 e. RR'), mm, last], '( ( ( abs ` ( F ` y ) ) x. %s ) x. %s ) <_ 9' % (EXX, GX))
        fin2 = w.s([m32, fin], 'eqbrtrd', '( %s -> %s <_ 9 )' % (Ae, NORM))
        return w.s([fin2], 'ex', '( %s -> ( ( Re ` y ) = %s -> %s <_ 9 ) )' % (Ay, Xe, NORM)), NORM
    eL, NL = edge(NH, None)
    eR, NR = edge(HALF, None)
    allL = w.s([eL], 'ralrimiva', '( %s -> A. y e. %s ( ( Re ` y ) = %s -> %s <_ 9 ) )' % (A, S, NH, NL))
    allR = w.s([eR], 'ralrimiva', '( %s -> A. y e. %s ( ( Re ` y ) = %s -> %s <_ 9 ) )' % (A, S, HALF, NR))
    # growth with y
    GRy = '( ( K e. RR+ /\\ B e. RR /\\ 0 <_ B ) /\\ A. y e. %s ( abs ` ( F ` y ) ) <_ ( K x. ( exp ` ( B x. ( abs ` ( Im ` y ) ) ) ) ) )' % S
    kb = D(w, A, 'simpld', [gr], '( K e. RR+ /\\ B e. RR /\\ 0 <_ B )')
    gz = D(w, A, 'simprd', [gr], 'A. z e. %s ( abs ` ( F ` z ) ) <_ ( K x. ( exp ` ( B x. ( abs ` ( Im ` z ) ) ) ) )' % S)
    idz = w.s([], 'id', '( z = y -> z = y )')
    sc, _ = w.wcongr('( abs ` ( F ` z ) ) <_ ( K x. ( exp ` ( B x. ( abs ` ( Im ` z ) ) ) ) )', {'z': 'y'}, 'z = y', {'z': idz})
    cb = w.s([sc], 'cbvralvw', '( A. z e. %s ( abs ` ( F ` z ) ) <_ ( K x. ( exp ` ( B x. ( abs ` ( Im ` z ) ) ) ) ) <-> A. y e. %s ( abs ` ( F ` y ) ) <_ ( K x. ( exp ` ( B x. ( abs ` ( Im ` y ) ) ) ) ) )' % (S, S))
    gy = w.s([kb, w.s([gz, cb], 'sylib', '( %s -> A. y e. %s ( abs ` ( F ` y ) ) <_ ( K x. ( exp ` ( B x. ( abs ` ( Im ` y ) ) ) ) ) )' % (A, S))], 'jca', '( %s -> %s )' % (A, GRy))
    XY = w.s([nhr, hr], 'jca', '( %s -> ( -u ( 1 / 2 ) e. RR /\\ ( 1 / 2 ) e. RR ) )' % A)
    PL1 = w.s([XY, hol3], 'jca', '( %s -> ( ( -u ( 1 / 2 ) e. RR /\\ ( 1 / 2 ) e. RR ) /\\ %s ) )' % (A, HOL3))
    PL2 = w.s([PL1, gy], 'jca', '( %s -> ( ( ( -u ( 1 / 2 ) e. RR /\\ ( 1 / 2 ) e. RR ) /\\ %s ) /\\ %s ) )' % (A, HOL3, GRy))
    n9 = w.s([w.s([], '9re', '9 e. RR'), w.s([], '9pos', '0 < 9')], 'elrpii' if False else 'idi', 'x') if False else None
    r9 = w.s([w.s([w.s([], '9nn', '9 e. NN'), w.inst('nnrp')], 'ax-mp', '9 e. RR+')], 'a1i', '( %s -> 9 e. RR+ )' % A)
    WPQ = w.s([wS, w.s([hr, lqr], 'jca', '( %s -> ( ( 1 / 2 ) e. RR /\\ %s e. RR ) )' % (A, LQ)), r9], '3jca',
              '( %s -> ( W e. %s /\\ ( ( 1 / 2 ) e. RR /\\ %s e. RR ) /\\ 9 e. RR+ ) )' % (A, S, LQ))
    EDG = '( A. y e. %s ( ( Re ` y ) = %s -> %s <_ 9 ) /\\ A. y e. %s ( ( Re ` y ) = %s -> %s <_ 9 ) )' % (S, NH, NL, S, HALF, NR)
    PL3 = w.s([WPQ, w.s([allL, allR], 'jca', '( %s -> %s )' % (A, EDG))], 'jca', '( %s -> ( ( W e. %s /\\ ( ( 1 / 2 ) e. RR /\\ %s e. RR ) /\\ 9 e. RR+ ) /\\ %s ) )' % (A, S, LQ, EDG))
    PLA = '( ( ( ( -u ( 1 / 2 ) e. RR /\\ ( 1 / 2 ) e. RR ) /\\ %s ) /\\ %s ) /\\ ( ( W e. %s /\\ ( ( 1 / 2 ) e. RR /\\ %s e. RR ) /\\ 9 e. RR+ ) /\\ %s ) )' % (HOL3, GRy, S, LQ, EDG)
    EW = '( exp ` ( ( ( Re ` W ) - ( 1 / 2 ) ) x. %s ) )' % LQ
    pl = w.s([w.s([PL2, PL3], 'jca', '( %s -> %s )' % (A, PLA)), w.inst('zl2pln')], 'syl', '( %s -> ( ( abs ` ( F ` W ) ) x. %s ) <_ 9 )' % (A, EW))
    # unwind: EW = Qd ^c ( ReW - 1/2 ), 9 / EW = 9 x. Qd ^c ( 1/2 - Re W )
    E1 = '( ( Re ` W ) - ( 1 / 2 ) )'
    e1r = D(w, A, 'resubcld', [wr, hr], '%s e. RR' % E1)
    qc = D(w, A, 'rpcnd', [qrp], '%s e. CC' % Qd); qne = D(w, A, 'rpne0d', [qrp], '%s =/= 0' % Qd)
    cxe = D(w, A, 'cxpefd', [qc, qne, D(w, A, 'recnd', [e1r], '%s e. CC' % E1)], '( %s ^c %s ) = %s' % (Qd, E1, EW))
    ewrp = D(w, A, 'rpcxpcld', [qrp, e1r], '( %s ^c %s ) e. RR+' % (Qd, E1))
    ewrp2 = w.s([cxe, ewrp], 'eqeltrrd' if False else 'idi', 'x') if False else w.s([w.s([cxe], 'eqcomd', '( %s -> %s = ( %s ^c %s ) )' % (A, EW, Qd, E1)), ewrp], 'eqeltrd', '( %s -> %s e. RR+ )' % (A, EW))
    fwc = w.s([w.s([ff, w.s([sd, wS], 'sseldd', '( %s -> W e. D )' % A)], 'ffvelcdmd', '( %s -> ( F ` W ) e. CC )' % A)], 'abscld', '( %s -> ( abs ` ( F ` W ) ) e. RR )' % A)
    ld = w.s([pl, w.s([fwc, a1(w, A, '9re', '9 e. RR'), w.s([D(w, A, 'rpred', [ewrp2], '%s e. RR' % EW), D(w, A, 'rpgt0d', [ewrp2], '0 < %s' % EW)], 'jca',
                                                                    '( %s -> ( %s e. RR /\\ 0 < %s ) )' % (A, EW, EW)), w.inst('lemuldiv')], 'syl3anc',
                                  '( %s -> ( ( ( abs ` ( F ` W ) ) x. %s ) <_ 9 <-> ( abs ` ( F ` W ) ) <_ ( 9 / %s ) ) )' % (A, EW, EW))], 'mpbid',
             '( %s -> ( abs ` ( F ` W ) ) <_ ( 9 / %s ) )' % (A, EW))
    E2 = '( ( 1 / 2 ) - ( Re ` W ) )'
    ng = D(w, A, 'negsubdi2d', [D(w, A, 'recnd', [wr], '( Re ` W ) e. CC'), a1(w, A, 'halfcn', '( 1 / 2 ) e. CC')], '-u %s = %s' % (E1, E2))
    cn = w.s([qc, qne, D(w, A, 'recnd', [e1r], '%s e. CC' % E1), w.inst('cxpneg')], 'syl3anc', '( %s -> ( %s ^c -u %s ) = ( 1 / ( %s ^c %s ) ) )' % (A, Qd, E1, Qd, E1))
    r1 = chain(w, A, ['( 9 / %s )' % EW, '( 9 x. ( 1 / %s ) )' % EW, '( 9 x. ( 1 / ( %s ^c %s ) ) )' % (Qd, E1), '( 9 x. ( %s ^c -u %s ) )' % (Qd, E1), '( 9 x. ( %s ^c %s ) )' % (Qd, E2)],
               [E(w, A, 'divrecd', [a1(w, A, '9cn', '9 e. CC'), D(w, A, 'rpcnd', [ewrp2], '%s e. CC' % EW), D(w, A, 'rpne0d', [ewrp2], '%s =/= 0' % EW)], '( 9 / %s )' % EW, '( 9 x. ( 1 / %s ) )' % EW),
                E(w, A, 'oveq2d', [E(w, A, 'oveq2d', [w.s([cxe], 'eqcomd', '( %s -> %s = ( %s ^c %s ) )' % (A, EW, Qd, E1))], '( 1 / %s )' % EW, '( 1 / ( %s ^c %s ) )' % (Qd, E1))],
                  '( 9 x. ( 1 / %s ) )' % EW, '( 9 x. ( 1 / ( %s ^c %s ) ) )' % (Qd, E1)),
                ('r', E(w, A, 'oveq2d', [cn], '( 9 x. ( %s ^c -u %s ) )' % (Qd, E1), '( 9 x. ( 1 / ( %s ^c %s ) ) )' % (Qd, E1))),
                E(w, A, 'oveq2d', [E(w, A, 'oveq2d', [ng], '( %s ^c -u %s )' % (Qd, E1), '( %s ^c %s )' % (Qd, E2))], '( 9 x. ( %s ^c -u %s ) )' % (Qd, E1), '( 9 x. ( %s ^c %s ) )' % (Qd, E2))])
    w.qed([ld, r1], 'breqtrd', L.STATEMENTS['zl3gint'])
    go(w)


# ---------------------------------------------------------------- zl3qbnd
if __name__ == '__main__' and want('zl3qbnd'):
    w = W('zl3qbnd', 'QBND of ~ zl2cvxe at the symmetric Gamma ratio ` Q ( z ) = pi ^ ( z - 1/2 ) Gamma ( ( 1 - z + P ) / 2 ) / Gamma ( ( z + P ) / 2 ) ` : '
          '` | Q ( z ) | <_ 12 ( | Im z | + 2 ) ^ ( 1/2 - Re z ) ` on ` -1/2 <_ Re z <_ 0 ` ( ~ zl3gint with the edges ~ zl3qex , ~ zl3qey , '
          'the growth ~ zl3qgr and the closed form ~ zl3qhol , ~ zl3qv ).')
    A = '( P e. { 0 , 1 } )'[2:-2]
    GOAL = L.STATEMENTS['zl3qbnd']
    ALLZ = GOAL.split(' -> ', 1)[1][:-2]
    SQ = L.SQ; FL = L.FL; QQ = L.QQP
    pu = w.s([w.s([w.s([], '0elunit', '0 e. ( 0 [,] 1 )'), w.s([], '1elunit', '1 e. ( 0 [,] 1 )'), w.inst('prssi')], 'mp2an', '{ 0 , 1 } C_ ( 0 [,] 1 )')],
             'a1i', '( %s -> { 0 , 1 } C_ ( 0 [,] 1 ) )' % A)
    pin = w.s([pu, w.s([], 'id', '( %s -> %s )' % (A, A))], 'sseldd', '( %s -> P e. ( 0 [,] 1 ) )' % A)
    pp1 = w.s([pin, w.s([], 'elicc01', '( P e. ( 0 [,] 1 ) <-> ( P e. RR /\\ 0 <_ P /\\ P <_ 1 ) )')], 'sylib', '( %s -> %s )' % (A, L.PP1))
    GRk = 'A. u e. %s ( abs ` ( %s ` u ) ) <_ ( k x. ( exp ` ( 1 x. ( abs ` ( Im ` u ) ) ) ) )' % (SQ, FL)
    Ak = '( %s /\\ ( k e. RR+ /\\ %s ) )' % (A, GRk)
    Az = '( %s /\\ z e. CC )' % Ak
    RZ = '( -u ( 1 / 2 ) <_ ( Re ` z ) /\\ ( Re ` z ) <_ 0 )'
    Ar = '( %s /\\ %s )' % (Az, RZ)
    La = lambda st, f, fr=A: w.s([st], 'ad3antrrr', '( %s -> %s )' % (Ar, f))
    P1 = La(pp1, L.PP1)
    pr = D(w, Ar, 'simp1d', [P1], 'P e. RR'); p0 = D(w, Ar, 'simp2d', [P1], '0 <_ P')
    PPs = w.s([pr, p0], 'jca', '( %s -> %s )' % (Ar, L.PP))
    zc = D(w, Ar, 'simplr', [], 'z e. CC')
    r1 = D(w, Ar, 'simprl', [], '-u ( 1 / 2 ) <_ ( Re ` z )'); r2 = D(w, Ar, 'simprr', [], '( Re ` z ) <_ 0')
    rz = D(w, Ar, 'recld', [zc], '( Re ` z ) e. RR')
    cl = Closure(w, Ar, {'( Re ` z )': ('RR', rz)})
    lo = linarith(w, Ar, [r1], '-u 1 < ( Re ` z )', closure=cl); hi = linarith(w, Ar, [r2], '( Re ` z ) < 1', closure=cl)
    hh = linarith(w, Ar, [r2], '( Re ` z ) <_ ( 1 / 2 )', closure=cl)
    qv = w.s([w.s([PPs, w.s([zc, lo, hi], '3jca', '( %s -> ( z e. CC /\\ -u 1 < ( Re ` z ) /\\ ( Re ` z ) < 1 ) )' % Ar)], 'jca',
                  '( %s -> ( %s /\\ ( z e. CC /\\ -u 1 < ( Re ` z ) /\\ ( Re ` z ) < 1 ) ) )' % (Ar, L.PP)), w.inst('zl3qv')], 'syl',
             '( %s -> ( ( %s ` z ) = ( %s ` z ) /\\ ( %s ` z ) e. CC ) )' % (Ar, QQ, FL, FL))
    qe = D(w, Ar, 'simpld', [qv], '( %s ` z ) = ( %s ` z )' % (QQ, FL)); flc = D(w, Ar, 'simprd', [qv], '( %s ` z ) e. CC' % FL)
    qqc = w.s([qe, flc], 'eqeltrd', '( %s -> ( %s ` z ) e. CC )' % (Ar, QQ))
    hol = w.s([PPs, w.inst('zl3qhol')], 'syl', '( %s -> %s )' % (Ar, L.HOLF(FL, L.DQ)))
    # SQ C_ DQ
    Ay = '( %s /\\ y e. %s )' % (Ar, SQ)
    ys = D(w, Ay, 'simpr', [], 'y e. %s' % SQ)
    yel = w.s([ys, w.s([], 'elstr', '( y e. %s <-> ( y e. CC /\\ ( Re ` y ) e. ( -u ( 1 / 2 ) [,] ( 1 / 2 ) ) ) )' % SQ)], 'sylib',
              '( %s -> ( y e. CC /\\ ( Re ` y ) e. ( -u ( 1 / 2 ) [,] ( 1 / 2 ) ) ) )' % Ay)
    yc = D(w, Ay, 'simpld', [yel], 'y e. CC')
    hr = a1(w, Ay, 'halfre', '( 1 / 2 ) e. RR')
    bi = w.s([D(w, Ay, 'renegcld', [hr], '-u ( 1 / 2 ) e. RR'), hr, w.inst('elicc2')], 'syl2anc',
             '( %s -> ( ( Re ` y ) e. ( -u ( 1 / 2 ) [,] ( 1 / 2 ) ) <-> ( ( Re ` y ) e. RR /\\ -u ( 1 / 2 ) <_ ( Re ` y ) /\\ ( Re ` y ) <_ ( 1 / 2 ) ) ) )' % Ay)
    r3 = w.s([D(w, Ay, 'simprd', [yel], '( Re ` y ) e. ( -u ( 1 / 2 ) [,] ( 1 / 2 ) )'), bi], 'mpbid',
             '( %s -> ( ( Re ` y ) e. RR /\\ -u ( 1 / 2 ) <_ ( Re ` y ) /\\ ( Re ` y ) <_ ( 1 / 2 ) ) )' % Ay)
    cly = Closure(w, Ay, {'( Re ` y )': ('RR', D(w, Ay, 'simp1d', [r3], '( Re ` y ) e. RR'))})
    ylo = linarith(w, Ay, [D(w, Ay, 'simp2d', [r3], '-u ( 1 / 2 ) <_ ( Re ` y )')], '-u 1 < ( Re ` y )', closure=cly)
    yhi = linarith(w, Ay, [D(w, Ay, 'simp3d', [r3], '( Re ` y ) <_ ( 1 / 2 )')], '( Re ` y ) < 1', closure=cly)
    ydq = ctx_from(w, Ay, 'y', ylo, yhi, yc, None)
    ss = w.s([w.s([ydq], 'ex', '( %s -> ( y e. %s -> y e. %s ) )' % (Ar, SQ, L.DQ))], 'ssrdv', '( %s -> %s C_ %s )' % (Ar, SQ, L.DQ))
    HOL3 = '( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) /\\ %s C_ %s )' % (FL, L.DQ, L.DQ, FL, SQ, L.DQ)
    hol3 = w.s([D(w, Ar, 'simpld', [hol], '%s e. ( %s -cn-> CC )' % (FL, L.DQ)), D(w, Ar, 'simprd', [hol], '%s C_ dom ( CC _D %s )' % (L.DQ, FL)), ss], '3jca', '( %s -> %s )' % (Ar, HOL3))
    # growth with u
    grk = w.s([w.s([], 'simplr' if False else 'idi', 'x')], 'idi', 'x') if False else None
    kk = w.s([w.s([D(w, Ak, 'simprl', [], 'k e. RR+')], 'adantr', '( %s -> k e. RR+ )' % Az)], 'adantr', '( %s -> k e. RR+ )' % Ar)
    gk = w.s([w.s([D(w, Ak, 'simprr', [], GRk)], 'adantr', '( %s -> %s )' % (Az, GRk))], 'adantr', '( %s -> %s )' % (Ar, GRk))
    GRu = 'A. u e. %s ( abs ` ( %s ` u ) ) <_ ( k x. ( exp ` ( 1 x. ( abs ` ( Im ` u ) ) ) ) )' % (SQ, FL)
    gu = gk
    kb = w.s([kk, a1(w, Ar, '1re', '1 e. RR'), D(w, Ar, 'ltled', [a1(w, Ar, '0re', '0 e. RR'), a1(w, Ar, '1re', '1 e. RR'), a1(w, Ar, '0lt1', '0 < 1')], '0 <_ 1')], '3jca',
             '( %s -> ( k e. RR+ /\\ 1 e. RR /\\ 0 <_ 1 ) )' % Ar)
    GRW = '( ( k e. RR+ /\\ 1 e. RR /\\ 0 <_ 1 ) /\\ %s )' % GRu
    grw = w.s([kb, gu], 'jca', '( %s -> %s )' % (Ar, GRW))
    # edges with u, proved under the bare antecedent
    PPa = w.s([w.s([pp1], 'simp1d', '( %s -> P e. RR )' % A), w.s([pp1], 'simp2d', '( %s -> 0 <_ P )' % A)], 'jca', '( %s -> %s )' % (A, L.PP))
    Au = '( %s /\\ u e. CC )' % A
    uc = D(w, Au, 'simpr', [], 'u e. CC')
    EL = 'A. u e. CC ( ( Re ` u ) = -u ( 1 / 2 ) -> ( abs ` ( %s ` u ) ) <_ ( ( abs ` ( Im ` u ) ) + 2 ) )' % FL
    ER = 'A. u e. CC ( ( Re ` u ) = ( 1 / 2 ) -> ( abs ` ( %s ` u ) ) <_ 1 )' % FL
    Aue = '( %s /\\ ( Re ` u ) = -u ( 1 / 2 ) )' % Au
    ex_ = w.s([w.s([w.s([w.s([pp1], 'adantr', '( %s -> %s )' % (Au, L.PP1))], 'adantr', '( %s -> %s )' % (Aue, L.PP1)),
                    w.s([w.s([uc], 'adantr', '( %s -> u e. CC )' % Aue), D(w, Aue, 'simpr', [], '( Re ` u ) = -u ( 1 / 2 )')], 'jca',
                        '( %s -> ( u e. CC /\\ ( Re ` u ) = -u ( 1 / 2 ) ) )' % Aue)], 'jca', '( %s -> ( %s /\\ ( u e. CC /\\ ( Re ` u ) = -u ( 1 / 2 ) ) ) )' % (Aue, L.PP1)),
               w.inst('zl3qex')], 'syl', '( %s -> ( abs ` ( %s ` u ) ) <_ ( ( abs ` ( Im ` u ) ) + 2 ) )' % (Aue, FL))
    elr0 = w.s([w.s([ex_], 'ex', '( %s -> ( ( Re ` u ) = -u ( 1 / 2 ) -> ( abs ` ( %s ` u ) ) <_ ( ( abs ` ( Im ` u ) ) + 2 ) ) )' % (Au, FL))], 'ralrimiva', '( %s -> %s )' % (A, EL))
    Auy = '( %s /\\ ( Re ` u ) = ( 1 / 2 ) )' % Au
    ey_ = w.s([w.s([w.s([w.s([PPa], 'adantr', '( %s -> %s )' % (Au, L.PP))], 'adantr', '( %s -> %s )' % (Auy, L.PP)),
                    w.s([w.s([uc], 'adantr', '( %s -> u e. CC )' % Auy), D(w, Auy, 'simpr', [], '( Re ` u ) = ( 1 / 2 )')], 'jca',
                        '( %s -> ( u e. CC /\\ ( Re ` u ) = ( 1 / 2 ) ) )' % Auy)], 'jca', '( %s -> ( %s /\\ ( u e. CC /\\ ( Re ` u ) = ( 1 / 2 ) ) ) )' % (Auy, L.PP)),
               w.inst('zl3qey')], 'syl', '( %s -> ( abs ` ( %s ` u ) ) <_ 1 )' % (Auy, FL))
    eyr0 = w.s([w.s([ey_], 'ex', '( %s -> ( ( Re ` u ) = ( 1 / 2 ) -> ( abs ` ( %s ` u ) ) <_ 1 ) )' % (Au, FL))], 'ralrimiva', '( %s -> %s )' % (A, ER))
    elr = La(elr0, EL); eyr = La(eyr0, ER)
    WW = '( z e. CC /\\ ( -u ( 1 / 2 ) <_ ( Re ` z ) /\\ ( Re ` z ) <_ ( 1 / 2 ) ) )'
    ww = w.s([zc, w.s([r1, hh], 'jca', '( %s -> ( -u ( 1 / 2 ) <_ ( Re ` z ) /\\ ( Re ` z ) <_ ( 1 / 2 ) ) )' % Ar)], 'jca', '( %s -> %s )' % (Ar, WW))
    GA = '( ( ( %s /\\ %s ) /\\ ( %s /\\ %s ) ) /\\ %s )' % (HOL3, GRW, EL, ER, WW)
    ga = w.s([w.s([w.s([hol3, grw], 'jca', '( %s -> ( %s /\\ %s ) )' % (Ar, HOL3, GRW)), w.s([elr, eyr], 'jca', '( %s -> ( %s /\\ %s ) )' % (Ar, EL, ER))], 'jca',
                  '( %s -> ( ( %s /\\ %s ) /\\ ( %s /\\ %s ) ) )' % (Ar, HOL3, GRW, EL, ER)), ww], 'jca', '( %s -> %s )' % (Ar, GA))
    XP = '( ( ( abs ` ( Im ` z ) ) + 2 ) ^c ( ( 1 / 2 ) - ( Re ` z ) ) )'
    gi = w.s([ga, w.inst('zl3gint')], 'syl', '( %s -> ( abs ` ( %s ` z ) ) <_ ( 9 x. %s ) )' % (Ar, FL, XP))
    aiz = D(w, Ar, 'abscld', [D(w, Ar, 'recnd', [D(w, Ar, 'imcld', [zc], '( Im ` z ) e. RR')], '( Im ` z ) e. CC')], '( abs ` ( Im ` z ) ) e. RR')
    aiz0 = D(w, Ar, 'absge0d', [D(w, Ar, 'recnd', [D(w, Ar, 'imcld', [zc], '( Im ` z ) e. RR')], '( Im ` z ) e. CC')], '0 <_ ( abs ` ( Im ` z ) )')
    qd = D(w, Ar, 'elrpd', [D(w, Ar, 'readdcld', [aiz, a1(w, Ar, '2re', '2 e. RR')], '( ( abs ` ( Im ` z ) ) + 2 ) e. RR'),
                            linarith(w, Ar, [aiz0], '0 < ( ( abs ` ( Im ` z ) ) + 2 )', closure=Closure(w, Ar, {'( abs ` ( Im ` z ) )': ('RR', aiz)}))], '( ( abs ` ( Im ` z ) ) + 2 ) e. RR+')
    xp = D(w, Ar, 'rpcxpcld', [qd, D(w, Ar, 'resubcld', [a1(w, Ar, 'halfre', '( 1 / 2 ) e. RR'), rz], '( ( 1 / 2 ) - ( Re ` z ) ) e. RR')], '%s e. RR+' % XP)
    n12 = w.s([w.s([w.s([w.s([], '1nn0', '1 e. NN0'), w.s([], '2nn', '2 e. NN')], 'decnncl', '; 1 2 e. NN')], 'nnrei', '; 1 2 e. RR')], 'a1i', '( %s -> ; 1 2 e. RR )' % Ar)
    le912 = linarith(w, Ar, [], '9 <_ ; 1 2')
    m = D(w, Ar, 'lemul1ad', [a1(w, Ar, '9re', '9 e. RR'), n12, D(w, Ar, 'rpred', [xp], '%s e. RR' % XP), D(w, Ar, 'rpge0d', [xp], '0 <_ %s' % XP), le912],
          '( 9 x. %s ) <_ ( ; 1 2 x. %s )' % (XP, XP))
    fl = D(w, Ar, 'letrd', [D(w, Ar, 'abscld', [flc], '( abs ` ( %s ` z ) ) e. RR' % FL), D(w, Ar, 'remulcld', [a1(w, Ar, '9re', '9 e. RR'), D(w, Ar, 'rpred', [xp], '%s e. RR' % XP)], '( 9 x. %s ) e. RR' % XP),
                            D(w, Ar, 'remulcld', [n12, D(w, Ar, 'rpred', [xp], '%s e. RR' % XP)], '( ; 1 2 x. %s ) e. RR' % XP), gi, m], '( abs ` ( %s ` z ) ) <_ ( ; 1 2 x. %s )' % (FL, XP))
    qb = w.s([E(w, Ar, 'fveq2d', [qe], '( abs ` ( %s ` z ) )' % QQ, '( abs ` ( %s ` z ) )' % FL), fl], 'eqbrtrd', '( %s -> ( abs ` ( %s ` z ) ) <_ ( ; 1 2 x. %s ) )' % (Ar, QQ, XP))
    CONJ = '( ( %s ` z ) e. CC /\\ ( abs ` ( %s ` z ) ) <_ ( ; 1 2 x. %s ) )' % (QQ, QQ, XP)
    cj = w.s([qqc, qb], 'jca', '( %s -> %s )' % (Ar, CONJ))
    imp = w.s([cj], 'ex', '( %s -> ( %s -> %s ) )' % (Az, RZ, CONJ))
    allz = w.s([imp], 'ralrimiva', '( %s -> %s )' % (Ak, ALLZ))
    lim = w.s([allz], 'rexlimdvaa', '( %s -> ( E. k e. RR+ %s -> %s ) )' % (A, GRk, ALLZ))
    gr = w.s([pp1, w.inst('zl3qgr')], 'syl', '( %s -> E. k e. RR+ %s )' % (A, GRk))
    w.qed([gr, lim], 'mpd', GOAL)
    go(w)
