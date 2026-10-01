"""T7: the interfaces of the concrete handlers (blueprint D4): the mover's
(at S and at the pinned class, in the two binder forms), dropNum's, the strip
loop's, popBit's; and the small lemma inl =/= inr."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t7lib import *

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL


def tmcinlne():
    lab = 'tmcinlne'
    ph = 'A e. V'
    w = W(lab, 'A loaded register ` some a ` differs from the empty one ` none ` (` inl ` versus ` inr ` ).')
    a1 = w.s([], 'inlval', '( %s -> ( inl ` A ) = <. (/) , A >. )' % ph)
    z0 = w.s([], '0ex', '(/) e. _V')
    a2 = w.s([z0, w.inst('inrval')], 'ax-mp', '( inr ` (/) ) = <. 1o , (/) >.')
    a2a = w.s([a2], 'a1i', '( %s -> ( inr ` (/) ) = <. 1o , (/) >. )' % ph)
    a3 = w.s([a1, a2a], 'eqeq12d', '( %s -> ( ( inl ` A ) = ( inr ` (/) ) <-> <. (/) , A >. = <. 1o , (/) >. ) )' % ph)
    z0a = w.s([z0], 'a1i', '( %s -> (/) e. _V )' % ph)
    av = w.s([], 'elex', '( %s -> A e. _V )' % ph)
    a4 = w.s([z0a, av, w.inst('opthg')], 'syl2anc', '( %s -> ( <. (/) , A >. = <. 1o , (/) >. <-> ( (/) = 1o /\\ A = (/) ) ) )' % ph)
    a5 = w.s([a3, a4], 'bitrd', '( %s -> ( ( inl ` A ) = ( inr ` (/) ) <-> ( (/) = 1o /\\ A = (/) ) ) )' % ph)
    n1 = w.s([], '1n0', '1o =/= (/)')
    n2 = w.s([n1], 'nesymi', '-. (/) = 1o')
    n3 = w.s([n2], 'intnanr', '-. ( (/) = 1o /\\ A = (/) )')
    n3a = w.s([n3], 'a1i', '( %s -> -. ( (/) = 1o /\\ A = (/) ) )' % ph)
    w.qed([a5, n3a], 'mtbird', '( %s -> -. ( inl ` A ) = ( inr ` (/) ) )' % ph)
    return w.run()


def mover(lab, cls, member, gform, mbind):
    """the mover interface: cls 'S' (all states) or 'NP'; member: the closure conjunct;
    gform: the pushed letter as ( GID ` z ); mbind: the exit binder"""
    Ncls = 'TMSt' if cls == 'S' else NPC
    desc = {'tmcmvi': 'The mover\'s read interface at the concrete handlers over all states (T5\'s ` HCmov ` / ` HEmov ` '
                      'of ~ tm2fdup ): ` readA ` on a bit sets ` ra ` , the branch ` ra.isSome ` is taken and the letter '
                      'pushed by ` bitOf ra ` is the letter popped; on the terminator ` 4 ` the branch fails.',
            'tmcmvin': 'The mover\'s read interface at the concrete handlers inside a class of states with ` flag ` , '
                       '` cmp ` and ` carry ` pinned (the form of ~ tm2fmvn , ~ tm2fiz , ~ tm2fincr ): ` readA ` touches '
                       'only ` ra ` and ` da ` , so the class is preserved.',
            'tmcmving': 'The mover\'s read interface in the form of ~ tm2ftr and ~ tm2fcan (the letter map the identity '
                        'on the bit letters, the exit clause bound by ` m ` ).'}[lab]
    w = W(lab, desc)
    # the bit clause
    ph = '( r e. %s /\\ z e. %s )' % (Ncls, BITS)
    rin = w.s([], 'simpl', '( %s -> r e. %s )' % (ph, Ncls))
    zz = w.s([], 'simpr', '( %s -> z e. %s )' % (ph, BITS))
    if cls == 'S':
        rr = rin
    else:
        rr, fl, cm, ca = np_out(w, ph, 'r', rin)
    N = NVA('r', 'z')
    nv = rd_bit(w, ph, 'A', 'r', 'z', rr, zz)
    c1, _ = cis_val(w, ph, nv, N)
    p1 = pbr_val(w, ph, nv, N, 'z', zz)
    if gform:
        g1 = w.s([zz, w.inst('fvresi')], 'syl', '( %s -> ( %s ` z ) = z )' % (ph, GID))
        p1 = w.s([p1, g1], 'eqtr4d', '( %s -> ( %s ` %s ) = ( %s ` z ) )' % (ph, PBR, N, GID))
        ptxt = '( %s ` %s ) = ( %s ` z )' % (PBR, N, GID)
    else:
        ptxt = '( %s ` %s ) = z' % (PBR, N)
    ctxt = '( %s ` %s ) = 1o' % (CIS, N)
    if member:
        m1 = np_keep(w, ph, nv, N, fl, cm, ca)
        body1 = '( %s /\\ %s /\\ %s e. %s )' % (ctxt, ptxt, N, Ncls)
        j1 = w.s([c1, p1, m1], '3jca', '( %s -> %s )' % (ph, body1))
    else:
        body1 = '( %s /\\ %s )' % (ctxt, ptxt)
        j1 = w.s([c1, p1], 'jca', '( %s -> %s )' % (ph, body1))
    r1 = w.s([j1], 'rgen2', 'A. r e. %s A. z e. %s %s' % (Ncls, BITS, body1))
    # the terminator clause, binder mbind
    ph2 = '%s e. %s' % (mbind, Ncls)
    rin2 = w.s([], 'id', '( %s -> %s e. %s )' % (ph2, mbind, Ncls))
    if cls == 'S':
        rr2 = rin2
    else:
        rr2, fl2, cm2, ca2 = np_out(w, ph2, mbind, rin2)
    N2 = NVA(mbind, '4')
    nv2 = rd_comma(w, ph2, 'A', mbind, rr2)
    c2, _ = cis_val(w, ph2, nv2, N2)
    n0 = w.s([], '1n0', '1o =/= (/)')
    n0b = w.s([n0], 'nesymi', '-. (/) = 1o')
    n0a = w.s([n0b], 'a1i', '( %s -> -. (/) = 1o )' % ph2)
    e2 = w.s([c2], 'eqeq1d', '( %s -> ( ( %s ` %s ) = 1o <-> (/) = 1o ) )' % (ph2, CIS, N2))
    c2n = w.s([e2, n0a], 'mtbird', '( %s -> -. ( %s ` %s ) = 1o )' % (ph2, CIS, N2))
    if member:
        m2 = np_keep(w, ph2, nv2, N2, fl2, cm2, ca2)
        body2 = '( -. ( %s ` %s ) = 1o /\\ %s e. %s )' % (CIS, N2, N2, Ncls)
        j2 = w.s([c2n, m2], 'jca', '( %s -> %s )' % (ph2, body2))
    else:
        body2 = '-. ( %s ` %s ) = 1o' % (CIS, N2)
        j2 = c2n
    r2 = w.s([j2], 'ralrimiv' if False else 'rgen', 'A. %s e. %s %s' % (mbind, Ncls, body2))
    w.qed([r1, r2], 'pm3.2i', '( A. r e. %s A. z e. %s %s /\\ A. %s e. %s %s )' % (Ncls, BITS, body1, mbind, Ncls, body2))
    return w.run()


def tmcdri():
    lab = 'tmcdri'
    w = W(lab, 'The read interface of ` dropNum ` at the concrete handlers (T1\'s ` HCDR ` / ` HEDR ` of ~ tm2fdrop ): '
               'the branch ` ra.isSome ` after ` readA ` is taken on a bit and fails on the terminator.')
    ph = '( r e. TMSt /\\ z e. %s )' % BITS
    rr = w.s([], 'simpl', '( %s -> r e. TMSt )' % ph)
    zz = w.s([], 'simpr', '( %s -> z e. %s )' % (ph, BITS))
    N = NVA('r', 'z')
    nv = rd_bit(w, ph, 'A', 'r', 'z', rr, zz)
    c1, _ = cis_val(w, ph, nv, N)
    r1 = w.s([c1], 'rgen2', 'A. r e. TMSt A. z e. %s ( %s ` %s ) = 1o' % (BITS, CIS, N))
    ph2 = 'r e. TMSt'
    rr2 = w.s([], 'id', '( %s -> r e. TMSt )' % ph2)
    N2 = NVA('r', '4')
    nv2 = rd_comma(w, ph2, 'A', 'r', rr2)
    c2, _ = cis_val(w, ph2, nv2, N2)
    n0 = w.s([], '1n0', '1o =/= (/)')
    n0b = w.s([n0], 'nesymi', '-. (/) = 1o')
    n0a = w.s([n0b], 'a1i', '( %s -> -. (/) = 1o )' % ph2)
    e2 = w.s([c2], 'eqeq1d', '( %s -> ( ( %s ` %s ) = 1o <-> (/) = 1o ) )' % (ph2, CIS, N2))
    c2n = w.s([e2, n0a], 'mtbird', '( %s -> -. ( %s ` %s ) = 1o )' % (ph2, CIS, N2))
    r2 = w.s([c2n], 'rgen', 'A. r e. TMSt -. ( %s ` %s ) = 1o' % (CIS, N2))
    w.qed([r1, r2], 'pm3.2i', ST_DRI)
    return w.run()


if __name__ == '__main__':
    if want('tmcinlne'): tmcinlne()
    if want('tmcmvi'): mover('tmcmvi', 'S', False, False, 'r')
    if want('tmcdri'): tmcdri()
    if want('tmcmvin'): mover('tmcmvin', 'NP', True, False, 'r')
    if want('tmcmving'): mover('tmcmving', 'NP', True, True, 'm')


def tmcinl11():
    lab = 'tmcinl11'
    ph = '( A e. V /\\ B e. W )'
    w = W(lab, 'The register loader ` some ` is injective (` inl ` on the payloads).')
    av = w.s([], 'simpl', '( %s -> A e. V )' % ph); bv = w.s([], 'simpr', '( %s -> B e. W )' % ph)
    a1 = w.s([av, w.inst('inlval')], 'syl', '( %s -> ( inl ` A ) = <. (/) , A >. )' % ph)
    b1 = w.s([bv, w.inst('inlval')], 'syl', '( %s -> ( inl ` B ) = <. (/) , B >. )' % ph)
    e = w.s([a1, b1], 'eqeq12d', '( %s -> ( ( inl ` A ) = ( inl ` B ) <-> <. (/) , A >. = <. (/) , B >. ) )' % ph)
    z0 = w.s([], '0ex', '(/) e. _V'); z0a = w.s([z0], 'a1i', '( %s -> (/) e. _V )' % ph)
    o = w.s([z0a, av, w.inst('opthg')], 'syl2anc', '( %s -> ( <. (/) , A >. = <. (/) , B >. <-> ( (/) = (/) /\\ A = B ) ) )' % ph)
    i = w.s([], 'eqid', '(/) = (/)')
    b = w.s([i], 'biantrur', '( A = B <-> ( (/) = (/) /\\ A = B ) )')
    ba = w.s([b], 'a1i', '( %s -> ( A = B <-> ( (/) = (/) /\\ A = B ) ) )' % ph)
    o2 = w.s([o, ba], 'bitr4d', '( %s -> ( <. (/) , A >. = <. (/) , B >. <-> A = B ) )' % ph)
    w.qed([e, o2], 'bitrd', '( %s -> ( ( inl ` A ) = ( inl ` B ) <-> A = B ) )' % ph)
    return w.run()


def tmcspi():
    lab = 'tmcspi'
    PH = "( Y e. Gamma' /\\ Y =/= <. 1 , (/) >. )"
    w = W(lab, 'The strip loop\'s interface at the concrete handlers (T-MD\'s ` HSPC2 ` / ` HSPE2 ` of ~ tm2fcan ): '
               '` peek readA ` on a zero bit satisfies ` ra = some false ` and the identity pop keeps the state; '
               'on any other letter ` Y ` (the top bit ` <. 1 , 1o >. ` , or the terminator ` 4 ` when the '
               'value is ` 0 ` ) the test fails.  ` flag ` , ` cmp ` , ` carry ` are preserved throughout.')
    # part 1: closed
    ph = '( r e. %s /\\ z e. %s )' % (NPC, B0)
    rin = w.s([], 'simpl', '( %s -> r e. %s )' % (ph, NPC))
    zs = w.s([], 'simpr', '( %s -> z e. %s )' % (ph, B0))
    rr, fl, cm, ca = np_out(w, ph, 'r', rin)
    ze = w.s([zs, w.inst('elsni')], 'syl', '( %s -> z = %s )' % (ph, BIT0))
    one = w.s([w.s([], 'ax-1cn', '1 e. CC')], 'elexi', '1 e. _V')
    b0 = w.s([w.s([one, w.inst('snidg')], 'ax-mp', '1 e. { 1 }'), w.s([], '0el2o', '(/) e. 2o'), w.inst('opelxpi')], 'mp2an', '%s e. %s' % (BIT0, BITS))
    zz = w.s([ze, w.s([b0], 'a1i', '( %s -> %s e. %s )' % (ph, BIT0, BITS))], 'eqeltrd', '( %s -> z e. %s )' % (ph, BITS))
    N = NVA('r', 'z')
    nv = rd_bit(w, ph, 'A', 'r', 'z', rr, zz)
    z2 = w.s([ze], 'fveq2d', '( %s -> ( 2nd ` z ) = ( 2nd ` %s ) )' % (ph, BIT0))
    z2b = w.s([one, w.s([], '0ex', '(/) e. _V'), w.inst('op2ndg')], 'mp2an', '( 2nd ` %s ) = (/)' % BIT0)
    z2c = w.s([z2, w.s([z2b], 'a1i', '( %s -> ( 2nd ` %s ) = (/) )' % (ph, BIT0))], 'eqtrd', '( %s -> ( 2nd ` z ) = (/) )' % ph)
    rai = w.s([z2c], 'fveq2d', '( %s -> ( inl ` ( 2nd ` z ) ) = ( inl ` (/) ) )' % ph)
    dec = w.s([nv['fields']['ra'], rai], 'eqtrd', '( %s -> ( TMra ` %s ) = ( inl ` (/) ) )' % (ph, N))
    c1, _ = cra_val(w, ph, nv, N, '(/)', dec)
    # the identity pop
    bs = closed(w, ph, 'tm2lbits', "( { 1 } X. 2o ) C_ Gamma'")
    zg = w.s([bs, zz], 'sseldd', "( %s -> z e. Gamma' )" % ph)
    oz = w.s([zg, w.inst('djulcl')], 'syl', '( %s -> ( inl ` z ) e. %s )' % (ph, OPT))
    pr = w.s([nv['mem'], oz], 'opelxpd', '( %s -> <. %s , ( inl ` z ) >. e. ( TMSt X. %s ) )' % (ph, N, OPT))
    fr = w.s([pr, w.inst('fvres')], 'syl', '( %s -> ( %s ` <. %s , ( inl ` z ) >. ) = ( 1st ` <. %s , ( inl ` z ) >. ) )' % (ph, PID, N, N))
    o1 = w.s([nv['mem'], oz, w.inst('op1stg')], 'syl2anc', '( %s -> ( 1st ` <. %s , ( inl ` z ) >. ) = %s )' % (ph, N, N))
    pv = w.s([fr, o1], 'eqtrd', '( %s -> ( %s ` <. %s , ( inl ` z ) >. ) = %s )' % (ph, PID, N, N))
    m1 = np_keep(w, ph, nv, N, fl, cm, ca)
    m1b = w.s([pv, m1], 'eqeltrd', '( %s -> ( %s ` <. %s , ( inl ` z ) >. ) e. %s )' % (ph, PID, N, NPC))
    body1 = '( ( %s ` %s ) = 1o /\\ ( %s ` <. %s , ( inl ` z ) >. ) e. %s )' % (CRA0, N, PID, N, NPC)
    j1 = w.s([c1, m1b], 'jca', '( %s -> %s )' % (ph, body1))
    r1 = w.s([j1], 'rgen2', 'A. r e. %s A. z e. %s %s' % (NPC, B0, body1))
    r1a = w.s([r1], 'a1i', '( %s -> A. r e. %s A. z e. %s %s )' % (PH, NPC, B0, body1))
    # part 2
    ph2 = '( %s /\\ m e. %s )' % (PH, NPC)
    yg = w.s([w.s([], 'simpl', '( %s -> %s )' % (ph2, PH))], 'simpld', "( %s -> Y e. Gamma' )" % ph2)
    yn = w.s([w.s([], 'simpl', '( %s -> %s )' % (ph2, PH))], 'simprd', '( %s -> Y =/= %s )' % (ph2, BIT0))
    min_ = w.s([], 'simpr', '( %s -> m e. %s )' % (ph2, NPC))
    mm, fl2, cm2, ca2 = np_out(w, ph2, 'm', min_)
    N2 = NVA('m', 'Y')
    body2 = '( -. ( %s ` %s ) = 1o /\\ %s e. %s )' % (CRA0, N2, N2, NPC)
    # case a: Y a bit
    pha = '( %s /\\ Y e. %s )' % (ph2, BITS)
    ya = w.s([], 'simpr', '( %s -> Y e. %s )' % (pha, BITS))
    mma = w.s([mm], 'adantr', '( %s -> m e. TMSt )' % pha)
    nva = rd_bit(w, pha, 'A', 'm', 'Y', mma, ya)
    yop = w.s([ya, w.inst('tmcbitop')], 'syl', '( %s -> Y = <. 1 , ( 2nd ` Y ) >. )' % pha)
    yna = w.s([yn], 'adantr', '( %s -> Y =/= %s )' % (pha, BIT0))
    ynn = w.s([yna], 'neneqd', '( %s -> -. Y = %s )' % (pha, BIT0))
    e1 = w.s([yop], 'eqeq1d', '( %s -> ( Y = %s <-> <. 1 , ( 2nd ` Y ) >. = %s ) )' % (pha, BIT0, BIT0))
    n1 = w.s([e1, ynn], 'mtbid', '( %s -> -. <. 1 , ( 2nd ` Y ) >. = %s )' % (pha, BIT0))
    o2 = w.s([], 'opeq2', '( ( 2nd ` Y ) = (/) -> <. 1 , ( 2nd ` Y ) >. = %s )' % BIT0)
    n2 = w.s([n1, o2], 'nsyl', '( %s -> -. ( 2nd ` Y ) = (/) )' % pha)
    y2v = w.s([], 'fvexd', '( %s -> ( 2nd ` Y ) e. _V )' % pha)
    z0d = w.s([w.s([], '0ex', '(/) e. _V')], 'a1i', '( %s -> (/) e. _V )' % pha)
    i11 = w.s([y2v, z0d, w.inst('tmcinl11')], 'syl2anc', '( %s -> ( ( inl ` ( 2nd ` Y ) ) = ( inl ` (/) ) <-> ( 2nd ` Y ) = (/) ) )' % pha)
    n3 = w.s([i11, n2], 'mtbird', '( %s -> -. ( inl ` ( 2nd ` Y ) ) = ( inl ` (/) ) )' % pha)
    e4 = w.s([nva['fields']['ra']], 'eqeq1d', '( %s -> ( ( TMra ` %s ) = ( inl ` (/) ) <-> ( inl ` ( 2nd ` Y ) ) = ( inl ` (/) ) ) )' % (pha, N2))
    deca = w.s([e4, n3], 'mtbird', '( %s -> -. ( TMra ` %s ) = ( inl ` (/) ) )' % (pha, N2))
    ca_, _ = cra_val(w, pha, nva, N2, '(/)', deca)
    cna = not1o(w, pha, ca_, CRA0, N2)
    fla, cma, caa = [w.s([x], 'adantr', formula(w, x).replace('( %s ->' % ph2, '( %s ->' % pha, 1)) for x in (fl2, cm2, ca2)]
    ma = np_keep(w, pha, nva, N2, fla, cma, caa)
    ja = w.s([cna, ma], 'jca', '( %s -> %s )' % (pha, body2))
    # case b: Y not a bit
    phb = '( %s /\\ -. Y e. %s )' % (ph2, BITS)
    ynb = w.s([], 'simpr', '( %s -> -. Y e. %s )' % (phb, BITS))
    mmb = w.s([mm], 'adantr', '( %s -> m e. TMSt )' % phb)
    ygb = w.s([yg], 'adantr', "( %s -> Y e. Gamma' )" % phb)
    nvb = rd_nb(w, phb, 'A', 'm', 'Y', mmb, ygb, ynb)
    z0e = w.s([], '0ex', '(/) e. _V')
    ne = w.s([z0e, w.inst('tmcinlne')], 'ax-mp', '-. ( inl ` (/) ) = %s' % NONE)
    ne2 = w.s([ne], 'eqcomd' if False else 'a1i', '( %s -> -. ( inl ` (/) ) = %s )' % (phb, NONE))
    ec = w.s([], 'eqcom', '( %s = ( inl ` (/) ) <-> ( inl ` (/) ) = %s )' % (NONE, NONE))
    eca = w.s([ec], 'a1i', '( %s -> ( %s = ( inl ` (/) ) <-> ( inl ` (/) ) = %s ) )' % (phb, NONE, NONE))
    ne3 = w.s([eca, ne2], 'mtbird', '( %s -> -. %s = ( inl ` (/) ) )' % (phb, NONE))
    e5 = w.s([nvb['fields']['ra']], 'eqeq1d', '( %s -> ( ( TMra ` %s ) = ( inl ` (/) ) <-> %s = ( inl ` (/) ) ) )' % (phb, N2, NONE))
    decb = w.s([e5, ne3], 'mtbird', '( %s -> -. ( TMra ` %s ) = ( inl ` (/) ) )' % (phb, N2))
    cb_, _ = cra_val(w, phb, nvb, N2, '(/)', decb)
    cnb = not1o(w, phb, cb_, CRA0, N2)
    flb, cmb, cab = [w.s([x], 'adantr', formula(w, x).replace('( %s ->' % ph2, '( %s ->' % phb, 1)) for x in (fl2, cm2, ca2)]
    mb = np_keep(w, phb, nvb, N2, flb, cmb, cab)
    jb = w.s([cnb, mb], 'jca', '( %s -> %s )' % (phb, body2))
    j2 = w.s([ja, jb], 'pm2.61dan', '( %s -> %s )' % (ph2, body2))
    r2 = w.s([j2], 'ralrimiva', '( %s -> A. m e. %s %s )' % (PH, NPC, body2))
    w.qed([r1a, r2], 'jca', ST_SPI)
    return w.run()


def tmcpbi():
    lab = 'tmcpbi'
    PH = 'Z e. %s' % BITS
    w = W(lab, '` readBit ` on a bit letter lands, from every state, in the class with ` ra ` loaded and ` da ` '
               'clear (Lean ` popBit_runs_bit ` ; the interface of ~ tm2fpopn and of the loops of ~ tm2fml ).')
    ph = '( %s /\\ r e. TMSt )' % PH
    zz = w.s([], 'simpl', '( %s -> Z e. %s )' % (ph, BITS))
    rr = w.s([], 'simpr', '( %s -> r e. TMSt )' % ph)
    N = NVF('TMrdBit', 'r', 'Z')
    nv = rd_bit(w, ph, 'Bit', 'r', 'Z', rr, zz)
    cond = lambda t: '( ( TMra ` %s ) = ( inl ` ( 2nd ` Z ) ) /\\ ( TMda ` %s ) = (/) )' % (t, t)
    cs = w.s([nv['fields']['ra'], nv['fields']['da']], 'jca', '( %s -> %s )' % (ph, cond(N)))
    m = rab_in(w, ph, NRA('Z'), cond, N, nv['mem'], cs)
    w.qed([m], 'ralrimiva', ST_PBI)
    return w.run()


def tmcpei():
    lab = 'tmcpei'
    w = W(lab, '` readBit ` on the terminator sets ` da ` from every state (Lean ` popBit_runs_end ` ).')
    ph = 'r e. TMSt'
    rr = w.s([], 'id', '( %s -> r e. TMSt )' % ph)
    N = NVF('TMrdBit', 'r', '4')
    nv = rd_comma(w, ph, 'Bit', 'r', rr)
    cond = lambda t: '( TMda ` %s ) = 1o' % t
    m = rab_in(w, ph, NDA, cond, N, nv['mem'], nv['fields']['da'])
    w.qed([m], 'rgen', ST_PEI)
    return w.run()


if __name__ == '__main__':
    if want('tmcinl11'): tmcinl11()
    if want('tmcspi'): tmcspi()
    if want('tmcpbi'): tmcpbi()
    if want('tmcpei'): tmcpei()
