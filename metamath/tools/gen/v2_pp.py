"""Sortie v2: primprodub, the exponential bound for a product over the primes up to M."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from tm import W

PM = '( ( 1 ... M ) i^i Prime )'
def TRM(v): return '( 1 + ( C / ( %s x. ( %s - 1 ) ) ) )' % (v, v)
IFT = 'if ( p e. Prime , %s , 1 )' % TRM('p')
AN = '( M e. NN /\\ C e. RR+ )'
BP = '( ( M e. NN /\\ C e. RR+ ) /\\ p e. %s )' % PM
BF = '( ( M e. NN /\\ C e. RR+ ) /\\ p e. ( 2 ... M ) )'
BD = '( ( M e. NN /\\ C e. RR+ ) /\\ p e. ( ( 2 ... M ) \\ %s ) )' % PM


def ppsub():
    w = W('ppsub', 'The primes up to M lie in ( 2 ... M ).')
    def st(hyps, ref, f, ante=BP):
        return w.s(hyps, ref, '( %s -> %s )' % (ante, f))
    pin = w.s([], 'simpr', '( %s -> p e. %s )' % (BP, PM))
    pfz = st([pin, w.inst('elinel1')], 'syl', 'p e. ( 1 ... M )')
    ppr = st([pin, w.inst('elinel2')], 'syl', 'p e. Prime')
    pz = st([pfz, w.inst('elfzelz')], 'syl', 'p e. ZZ')
    ple = st([pfz, w.inst('elfzle2')], 'syl', 'p <_ M')
    puz = st([ppr, w.inst('prmuz2')], 'syl', 'p e. ( ZZ>= ` 2 )')
    ez = st([w.s([], 'eluz2', '( p e. ( ZZ>= ` 2 ) <-> ( 2 e. ZZ /\\ p e. ZZ /\\ 2 <_ p ) )')],
            'a1i', '( p e. ( ZZ>= ` 2 ) <-> ( 2 e. ZZ /\\ p e. ZZ /\\ 2 <_ p ) )')
    ez2 = st([ez, puz], 'mpbid', '( 2 e. ZZ /\\ p e. ZZ /\\ 2 <_ p )')
    p2 = st([ez2], 'simp3d', '2 <_ p')
    m = st([], 'simpll', 'M e. NN')
    mz = st([m], 'nnzd', 'M e. ZZ')
    tz = st([w.s([], '2z', '2 e. ZZ')], 'a1i', '2 e. ZZ')
    bi = st([pz, tz, mz, w.inst('elfz')], 'syl3anc',
            '( p e. ( 2 ... M ) <-> ( 2 <_ p /\\ p <_ M ) )')
    j = st([p2, ple], 'jca', '( 2 <_ p /\\ p <_ M )')
    inn = st([bi, j], 'mpbird', 'p e. ( 2 ... M )')
    ei = w.s([inn], 'ex', '( %s -> ( p e. %s -> p e. ( 2 ... M ) ) )' % (AN, PM))
    w.qed([ei], 'ssrdv', '( %s -> %s C_ ( 2 ... M ) )' % (AN, PM))
    return w


def ppnotprm():
    A = 'p e. ( ( 2 ... M ) \\ %s )' % PM
    w = W('ppnotprm', 'An element of ( 2 ... M ) outside the primes up to M is not prime.')
    def st(hyps, ref, f, ante=A):
        return w.s(hyps, ref, '( %s -> %s )' % (ante, f))
    pfz = st([], 'eldifi', 'p e. ( 2 ... M )')
    npm = st([], 'eldifn', '-. p e. %s' % PM)
    uz = st([w.s([], '2z', '2 e. ZZ')], 'a1i', '2 e. ZZ')
    ss = st([w.s([], '2eluzge1', '2 e. ( ZZ>= ` 1 )')], 'a1i', '2 e. ( ZZ>= ` 1 )')
    sub = st([ss, w.inst('fzss1')], 'syl', '( 2 ... M ) C_ ( 1 ... M )')
    p1 = st([sub, pfz], 'sseldd', 'p e. ( 1 ... M )')
    ei = st([p1], 'a1d', '( p e. Prime -> p e. ( 1 ... M ) )')
    idp = w.s([], 'id', '( p e. Prime -> p e. Prime )')
    idpa = st([idp], 'a1i', '( p e. Prime -> p e. Prime )')
    inm = st([ei, idpa], 'jcad', '( p e. Prime -> ( p e. ( 1 ... M ) /\\ p e. Prime ) )')
    elin = st([w.s([], 'elin', '( p e. %s <-> ( p e. ( 1 ... M ) /\\ p e. Prime ) )' % PM)],
              'a1i', '( p e. %s <-> ( p e. ( 1 ... M ) /\\ p e. Prime ) )' % PM)
    imp = st([inm, elin], 'sylibrd', '( p e. Prime -> p e. %s )' % PM)
    w.qed([imp, npm], 'mtod', '( %s -> -. p e. Prime )' % A)
    return w


def ppifle():
    w = W('ppifle', 'The primality indicator factor is at most the factor itself.')
    C1 = '( %s /\\ p e. Prime )' % BF
    C2 = '( %s /\\ -. p e. Prime )' % BF
    T = TRM('p')
    def st(hyps, ref, f, ante=BF):
        return w.s(hyps, ref, '( %s -> %s )' % (ante, f))
    crpf = st([], 'simplr', 'C e. RR+')
    pfz = st([], 'simpr', 'p e. ( 2 ... M )')
    prp = st([pfz, w.inst('fz2m1rp')], 'syl', '( p x. ( p - 1 ) ) e. RR+')
    trp = st([crpf, prp], 'rpdivcld', '( C / ( p x. ( p - 1 ) ) ) e. RR+')
    tr = st([trp], 'rpred', '( C / ( p x. ( p - 1 ) ) ) e. RR')
    t0 = st([trp], 'rpge0d', '0 <_ ( C / ( p x. ( p - 1 ) ) )')
    onef = w.s([], '1red', '( %s -> 1 e. RR )' % BF)
    trmr = st([onef, tr], 'readdcld', '%s e. RR' % T)
    # case p e. Prime
    pp1 = st([], 'simpr', 'p e. Prime', C1)
    ift = st([pp1], 'iftrued', '%s = %s' % (IFT, T), C1)
    trmr1 = st([trmr], 'adantr', '%s e. RR' % T, C1)
    leid = st([trmr1], 'leidd', '%s <_ %s' % (T, T), C1)
    case1 = st([ift, leid], 'eqbrtrd', '%s <_ %s' % (IFT, T), C1)
    # case -. p e. Prime
    np = st([], 'simpr', '-. p e. Prime', C2)
    iff = st([np], 'iffalsed', '%s = 1' % IFT, C2)
    one2 = w.s([], '1red', '( %s -> 1 e. RR )' % C2)
    tr2 = st([tr], 'adantr', '( C / ( p x. ( p - 1 ) ) ) e. RR', C2)
    t02 = st([t0], 'adantr', '0 <_ ( C / ( p x. ( p - 1 ) ) )', C2)
    bi = st([one2, tr2, w.inst('addge01')], 'syl2anc',
            '( 0 <_ ( C / ( p x. ( p - 1 ) ) ) <-> 1 <_ %s )' % T, C2)
    ge = st([bi, t02], 'mpbid', '1 <_ %s' % T, C2)
    case2 = st([iff, ge], 'eqbrtrd', '%s <_ %s' % (IFT, T), C2)
    w.qed([case1, case2], 'pm2.61dan', '( %s -> %s <_ %s )' % (BF, IFT, T))
    return w


def primprodub():
    w = W('primprodub',
          'The product of 1 + C / ( p x. ( p - 1 ) ) over the primes up to M is at most exp C.')
    PP = 'prod_ p e. %s %s' % (PM, TRM('p'))
    PI = 'prod_ p e. %s %s' % (PM, IFT)
    PIF = 'prod_ p e. ( 2 ... M ) %s' % IFT
    PF = 'prod_ p e. ( 2 ... M ) %s' % TRM('p')
    PN = 'prod_ n e. ( 2 ... M ) %s' % TRM('n')
    T = TRM('p')
    def st(hyps, ref, f, ante=AN):
        return w.s(hyps, ref, '( %s -> %s )' % (ante, f))
    ss = st([], 'ppsub', '%s C_ ( 2 ... M )' % PM)
    # on PM the indicator factor is the factor
    pinb = w.s([], 'simpr', '( %s -> p e. %s )' % (BP, PM))
    pprb = st([pinb, w.inst('elinel2')], 'syl', 'p e. Prime', BP)
    ift = st([pprb], 'iftrued', '%s = %s' % (IFT, T), BP)
    e1 = st([ift], 'prodeq2dv', '%s = %s' % (PI, PP))
    # the indicator factor is in CC on PM
    crpp = st([], 'simplr', 'C e. RR+', BP)
    puzb = st([pprb, w.inst('prmuz2')], 'syl', 'p e. ( ZZ>= ` 2 )', BP)
    prpb = st([puzb, w.inst('uz2m1rp')], 'syl', '( p x. ( p - 1 ) ) e. RR+', BP)
    trpb = st([crpp, prpb], 'rpdivcld', '( C / ( p x. ( p - 1 ) ) ) e. RR+', BP)
    tcb = st([trpb], 'rpcnd', '( C / ( p x. ( p - 1 ) ) ) e. CC', BP)
    oneb = w.s([], '1cnd', '( %s -> 1 e. CC )' % BP)
    tmcb = st([oneb, tcb], 'addcld', '%s e. CC' % T, BP)
    ifcb = st([ift, tmcb], 'eqeltrd', '%s e. CC' % IFT, BP)
    # off PM the indicator factor is 1
    npr = st([w.s([], 'simpr', '( %s -> p e. ( ( 2 ... M ) \\ %s ) )' % (BD, PM)), w.inst('ppnotprm')],
             'syl', '-. p e. Prime', BD)
    iff = st([npr], 'iffalsed', '%s = 1' % IFT, BD)
    fin = st([w.s([], 'fzfi', '( 2 ... M ) e. Fin')], 'a1i', '( 2 ... M ) e. Fin')
    e2 = st([ss, ifcb, iff, fin], 'fprodss', '%s = %s' % (PI, PIF))
    # fprodle on ( 2 ... M )
    crpf = st([], 'simpr', 'C e. RR+')
    crpf2 = st([crpf], 'adantr', 'C e. RR+', BF)
    pfz = w.s([], 'simpr', '( %s -> p e. ( 2 ... M ) )' % BF)
    prp = st([pfz, w.inst('fz2m1rp')], 'syl', '( p x. ( p - 1 ) ) e. RR+', BF)
    trp = st([crpf2, prp], 'rpdivcld', '( C / ( p x. ( p - 1 ) ) ) e. RR+', BF)
    tr = st([trp], 'rpred', '( C / ( p x. ( p - 1 ) ) ) e. RR', BF)
    t0 = st([trp], 'rpge0d', '0 <_ ( C / ( p x. ( p - 1 ) ) )', BF)
    onef = w.s([], '1red', '( %s -> 1 e. RR )' % BF)
    z1f = st([w.s([], '0le1', '0 <_ 1')], 'a1i', '0 <_ 1', BF)
    trmr = st([onef, tr], 'readdcld', '%s e. RR' % T, BF)
    trm0 = st([onef, tr, z1f, t0], 'addge0d', '0 <_ %s' % T, BF)
    ifr = st([trmr, onef], 'ifcld', '%s e. RR' % IFT, BF)
    b1 = w.s([], 'breq2', '( %s = %s -> ( 0 <_ %s <-> 0 <_ %s ) )' % (T, IFT, T, IFT))
    b2 = w.s([], 'breq2', '( 1 = %s -> ( 0 <_ 1 <-> 0 <_ %s ) )' % (IFT, IFT))
    h3 = st([trm0], 'adantr', '0 <_ %s' % T, '( %s /\\ p e. Prime )' % BF)
    h4 = st([z1f], 'adantr', '0 <_ 1', '( %s /\\ -. p e. Prime )' % BF)
    if0 = st([b1, b2, h3, h4], 'ifbothda', '0 <_ %s' % IFT, BF)
    ifle = st([], 'ppifle', '%s <_ %s' % (IFT, T), BF)
    nf = w.s([], 'nfv', 'F/ p %s' % AN)
    ple = st([nf, fin, ifr, if0, trmr, ifle], 'fprodle', '%s <_ %s' % (PIF, PF))
    # change of bound variable and prodefub
    cb = st([w.s([], 'cbvprodv', '%s = %s' % (PF, PN))], 'a1i', '%s = %s' % (PF, PN))
    pe = st([], 'prodefub', '%s <_ ( exp ` C )' % PN)
    pfle = st([cb, pe], 'eqbrtrd', '%s <_ ( exp ` C )' % PF)
    pifre = st([fin, ifr], 'fprodrecl', '%s e. RR' % PIF)
    pfre = st([fin, trmr], 'fprodrecl', '%s e. RR' % PF)
    cr = st([crpf], 'rpred', 'C e. RR')
    efre = st([cr], 'reefcld', '( exp ` C ) e. RR')
    tot = st([pifre, pfre, efre, ple, pfle], 'letrd', '%s <_ ( exp ` C )' % PIF)
    e12 = st([e1, e2], 'eqtr3d', '%s = %s' % (PP, PIF))
    w.qed([e12, tot], 'eqbrtrd', '( %s -> %s <_ ( exp ` C ) )' % (AN, PP))
    return w


if __name__ == '__main__':
    import sys
    for f in sys.argv[1:] or ['ppsub']:
        globals()[f]().run()
