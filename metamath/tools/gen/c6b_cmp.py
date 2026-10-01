"""Sortie C6b, part 5: the closed rectangle is closed and compact (crectcld,
crectcmp) and the zeros of a holomorphic function on it are finite (holzfi)."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')); from c6blib import *
import lin
from lin import linarith
lin.FASTPATH = True

RECT = '( A crect B )'
I1 = '( %s [,] %s )' % (RA, RB); I2 = '( %s [,] %s )' % (IA, IB)
RTOP = '( topGen ` ran (,) )'
CLS = '( Clsd ` %s )' % TOP
JR = '( %s |`t %s )' % (TOP, RECT)

if __name__ == '__main__':
    # ---- crectcld -----------------------------------------------------------------
    w = W('crectcld', 'A closed rectangle is a closed subset of the complex plane.')
    A0 = AB
    ac = w.s([], 'simpl', '( %s -> A e. CC )' % A0); bc = w.s([], 'simpr', '( %s -> B e. CC )' % A0)
    ar = w.s([ac], 'recld', '( %s -> %s e. RR )' % (A0, RA)); br = w.s([bc], 'recld', '( %s -> %s e. RR )' % (A0, RB))
    ai = w.s([ac], 'imcld', '( %s -> %s e. RR )' % (A0, IA)); bi = w.s([bc], 'imcld', '( %s -> %s e. RR )' % (A0, IB))
    # ( CC -cn-> RR ) = ( TOP Cn RTOP )
    ej = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
    ek = w.s([], 'eqid', '( %s |`t CC ) = ( %s |`t CC )' % (TOP, TOP))
    el = w.s([], 'eqid', '( %s |`t RR ) = ( %s |`t RR )' % (TOP, TOP))
    cnc = w.s([ej, ek, el], 'cncfcn', '( ( CC C_ CC /\\ RR C_ CC ) -> ( CC -cn-> RR ) = ( ( %s |`t CC ) Cn ( %s |`t RR ) ) )' % (TOP, TOP))
    cnc2 = w.s([w.s([], 'ssid', 'CC C_ CC'), w.s([], 'ax-resscn', 'RR C_ CC'), cnc], 'mp2an', '( CC -cn-> RR ) = ( ( %s |`t CC ) Cn ( %s |`t RR ) )' % (TOP, TOP))
    rid = w.s([w.s([ej], 'cnfldtop', '%s e. Top' % TOP), w.s([w.s([], 'unicntop', 'CC = U. %s' % TOP)], 'restid', '( %s e. Top -> ( %s |`t CC ) = %s )' % (TOP, TOP, TOP))], 'ax-mp', '( %s |`t CC ) = %s' % (TOP, TOP))
    tg = w.s([w.s([ej], 'tgioo2', '%s = ( %s |`t RR )' % (RTOP, TOP))], 'eqcomi', '( %s |`t RR ) = %s' % (TOP, RTOP))
    cnc3 = w.s([cnc2, w.s([rid, tg], 'oveq12i', '( ( %s |`t CC ) Cn ( %s |`t RR ) ) = ( %s Cn %s )' % (TOP, TOP, TOP, RTOP))], 'eqtri', '( CC -cn-> RR ) = ( %s Cn %s )' % (TOP, RTOP))
    recn = w.s([w.s([], 'recncf', 'Re e. ( CC -cn-> RR )'), cnc3], 'eleqtri', 'Re e. ( %s Cn %s )' % (TOP, RTOP))
    imcn = w.s([w.s([], 'imcncf', 'Im e. ( CC -cn-> RR )'), cnc3], 'eleqtri', 'Im e. ( %s Cn %s )' % (TOP, RTOP))
    c1 = w.s([w.s([recn], 'a1i', '( %s -> Re e. ( %s Cn %s ) )' % (A0, TOP, RTOP)), w.s([ar, br, w.inst('icccld')], 'syl2anc', '( %s -> %s e. ( Clsd ` %s ) )' % (A0, I1, RTOP)), w.inst('cnclima')], 'syl2anc',
             '( %s -> ( `\' Re " %s ) e. %s )' % (A0, I1, CLS))
    c2 = w.s([w.s([imcn], 'a1i', '( %s -> Im e. ( %s Cn %s ) )' % (A0, TOP, RTOP)), w.s([ai, bi, w.inst('icccld')], 'syl2anc', '( %s -> %s e. ( Clsd ` %s ) )' % (A0, I2, RTOP)), w.inst('cnclima')], 'syl2anc',
             '( %s -> ( `\' Im " %s ) e. %s )' % (A0, I2, CLS))
    cin = w.s([c1, c2, w.inst('incld')], 'syl2anc', '( %s -> ( ( `\' Re " %s ) i^i ( `\' Im " %s ) ) e. %s )' % (A0, I1, I2, CLS))
    # the rectangle is that intersection
    R1 = '{ z e. CC | ( Re ` z ) e. %s }' % I1; R2 = '{ z e. CC | ( Im ` z ) e. %s }' % I2
    R12 = '{ z e. CC | ( ( Re ` z ) e. %s /\\ ( Im ` z ) e. %s ) }' % (I1, I2)
    v1 = w.s([w.s([w.s([], 'ref', 'Re : CC --> RR'), w.inst('ffn')], 'ax-mp', 'Re Fn CC'), w.inst('fncnvima2')], 'ax-mp', '( `\' Re " %s ) = %s' % (I1, R1))
    v2 = w.s([w.s([w.s([], 'imf', 'Im : CC --> RR'), w.inst('ffn')], 'ax-mp', 'Im Fn CC'), w.inst('fncnvima2')], 'ax-mp', '( `\' Im " %s ) = %s' % (I2, R2))
    v12 = w.s([w.s([v1, v2], 'ineq12i', '( ( `\' Re " %s ) i^i ( `\' Im " %s ) ) = ( %s i^i %s )' % (I1, I2, R1, R2)), w.s([], 'inrab', '( %s i^i %s ) = %s' % (R1, R2, R12))], 'eqtri',
              '( ( `\' Re " %s ) i^i ( `\' Im " %s ) ) = %s' % (I1, I2, R12))
    cv = w.s([], 'crectval', '( %s -> %s = %s )' % (A0, RECT, R12))
    eq = w.s([cv, w.s([v12], 'eqcomi', '%s = ( ( `\' Re " %s ) i^i ( `\' Im " %s ) )' % (R12, I1, I2))], 'eqtrdi', '( %s -> %s = ( ( `\' Re " %s ) i^i ( `\' Im " %s ) ) )' % (A0, RECT, I1, I2))
    w.qed([eq, cin], 'eqeltrd', '( %s -> %s e. %s )' % (A0, RECT, CLS))
    run1(w)

    # ---- crectcmp -----------------------------------------------------------------
    w = W('crectcmp', 'A closed rectangle is compact.')
    A0 = AB
    ac = w.s([], 'simpl', '( %s -> A e. CC )' % A0); bc = w.s([], 'simpr', '( %s -> B e. CC )' % A0)
    ej = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
    et = w.s([], 'eqid', '%s = %s' % (JR, JR))
    BND = 'E. r e. RR A. x e. %s ( abs ` x ) <_ r' % RECT
    hb = w.s([w.s([], 'crectss', '( %s -> %s C_ CC )' % (A0, RECT)), w.s([ej, et], 'cnheibor', '( %s C_ CC -> ( %s e. Comp <-> ( %s e. %s /\\ %s ) ) )' % (RECT, JR, RECT, CLS, BND))], 'syl',
             '( %s -> ( %s e. Comp <-> ( %s e. %s /\\ %s ) ) )' % (A0, JR, RECT, CLS, BND))
    cld = w.s([], 'crectcld', '( %s -> %s e. %s )' % (A0, RECT, CLS))
    A1 = '( %s /\\ x e. %s )' % (A0, RECT)
    ab1 = w.s([], 'simpl', '( %s -> %s )' % (A1, AB))
    xin = w.s([], 'simpr', '( %s -> x e. %s )' % (A1, RECT))
    e = rectel(w, A1, xin, ab1, 'x')
    RX = RE('x'); IX = IM('x')
    RB_ = '( ( ( abs ` %s ) + ( abs ` %s ) ) + ( ( abs ` %s ) + ( abs ` %s ) ) )' % (RA, RB, IA, IB)
    def absparts(X, xr):
        n, p, a = absbnds(w, A1, X, xr)
        g0 = w.s([w.s([xr], 'recnd', '( %s -> %s e. CC )' % (A1, X))], 'absge0d', '( %s -> 0 <_ ( abs ` %s ) )' % (A1, X))
        return n, p, a, g0
    nA, pA, aA, gA = absparts(RA, e['ar']); nB, pB, aB, gB = absparts(RB, e['br'])
    nI, pI, aI, gI = absparts(IA, e['ai']); nJ, pJ, aJ, gJ = absparts(IB, e['bi'])
    leaves = {RA: ('RR', e['ar']), RB: ('RR', e['br']), IA: ('RR', e['ai']), IB: ('RR', e['bi']), RX: ('RR', e['xr']), IX: ('RR', e['xi']),
              '( abs ` %s )' % RA: ('RR', aA), '( abs ` %s )' % RB: ('RR', aB), '( abs ` %s )' % IA: ('RR', aI), '( abs ` %s )' % IB: ('RR', aJ)}
    SR = '( ( abs ` %s ) + ( abs ` %s ) )' % (RA, RB); SI = '( ( abs ` %s ) + ( abs ` %s ) )' % (IA, IB)
    r1 = linarith(w, A1, [e['lar'], nA, gB], '-u %s <_ %s' % (SR, RX), leaves=leaves)
    r2 = linarith(w, A1, [e['lbr'], pB, gA], '%s <_ %s' % (RX, SR), leaves=leaves)
    i1 = linarith(w, A1, [e['lai'], nI, gJ], '-u %s <_ %s' % (SI, IX), leaves=leaves)
    i2 = linarith(w, A1, [e['lbi'], pJ, gI], '%s <_ %s' % (IX, SI), leaves=leaves)
    srr = w.s([aA, aB], 'readdcld', '( %s -> %s e. RR )' % (A1, SR)); sir = w.s([aI, aJ], 'readdcld', '( %s -> %s e. RR )' % (A1, SI))
    lre = w.s([w.s([r1, r2], 'jca', '( %s -> ( -u %s <_ %s /\\ %s <_ %s ) )' % (A1, SR, RX, RX, SR)), w.s([e['xr'], srr, w.inst('absle')], 'syl2anc', '( %s -> ( ( abs ` %s ) <_ %s <-> ( -u %s <_ %s /\\ %s <_ %s ) ) )' % (A1, RX, SR, SR, RX, RX, SR))], 'mpbird',
              '( %s -> ( abs ` %s ) <_ %s )' % (A1, RX, SR))
    lim = w.s([w.s([i1, i2], 'jca', '( %s -> ( -u %s <_ %s /\\ %s <_ %s ) )' % (A1, SI, IX, IX, SI)), w.s([e['xi'], sir, w.inst('absle')], 'syl2anc', '( %s -> ( ( abs ` %s ) <_ %s <-> ( -u %s <_ %s /\\ %s <_ %s ) ) )' % (A1, IX, SI, SI, IX, IX, SI))], 'mpbird',
              '( %s -> ( abs ` %s ) <_ %s )' % (A1, IX, SI))
    # abs x <_ abs Re x + abs Im x
    xc = e['xc']
    rxc = w.s([e['xr']], 'recnd', '( %s -> %s e. CC )' % (A1, RX)); ixc = w.s([e['xi']], 'recnd', '( %s -> %s e. CC )' % (A1, IX))
    ic = closed(w, A1, 'ax-icn', '_i e. CC')
    iix = w.s([ic, ixc], 'mulcld', '( %s -> ( _i x. %s ) e. CC )' % (A1, IX))
    rl = w.s([xc], 'replimd', '( %s -> x = ( %s + ( _i x. %s ) ) )' % (A1, RX, IX))
    tri = w.s([rxc, iix], 'abstrid', '( %s -> ( abs ` ( %s + ( _i x. %s ) ) ) <_ ( ( abs ` %s ) + ( abs ` ( _i x. %s ) ) ) )' % (A1, RX, IX, RX, IX))
    aim = w.s([w.s([ic, ixc], 'absmuld', '( %s -> ( abs ` ( _i x. %s ) ) = ( ( abs ` _i ) x. ( abs ` %s ) ) )' % (A1, IX, IX)),
               w.s([w.s([closed(w, A1, 'absi', '( abs ` _i ) = 1')], 'oveq1d', '( %s -> ( ( abs ` _i ) x. ( abs ` %s ) ) = ( 1 x. ( abs ` %s ) ) )' % (A1, IX, IX)), w.s([w.s([w.s([ixc], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A1, IX))], 'recnd', '( %s -> ( abs ` %s ) e. CC )' % (A1, IX))], 'mullidd', '( %s -> ( 1 x. ( abs ` %s ) ) = ( abs ` %s ) )' % (A1, IX, IX))], 'eqtrd',
                   '( %s -> ( ( abs ` _i ) x. ( abs ` %s ) ) = ( abs ` %s ) )' % (A1, IX, IX))], 'eqtrd', '( %s -> ( abs ` ( _i x. %s ) ) = ( abs ` %s ) )' % (A1, IX, IX))
    tri2 = w.s([w.s([rl], 'fveq2d', '( %s -> ( abs ` x ) = ( abs ` ( %s + ( _i x. %s ) ) ) )' % (A1, RX, IX)), w.s([tri, w.s([aim], 'oveq2d', '( %s -> ( ( abs ` %s ) + ( abs ` ( _i x. %s ) ) ) = ( ( abs ` %s ) + ( abs ` %s ) ) )' % (A1, RX, IX, RX, IX))], 'breqtrd',
                                                                                                                '( %s -> ( abs ` ( %s + ( _i x. %s ) ) ) <_ ( ( abs ` %s ) + ( abs ` %s ) ) )' % (A1, RX, IX, RX, IX))], 'eqbrtrd',
               '( %s -> ( abs ` x ) <_ ( ( abs ` %s ) + ( abs ` %s ) ) )' % (A1, RX, IX))
    leaves2 = dict(leaves)
    leaves2['( abs ` x )'] = ('RR', w.s([xc], 'abscld', '( %s -> ( abs ` x ) e. RR )' % A1))
    leaves2['( abs ` %s )' % RX] = ('RR', w.s([rxc], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A1, RX)))
    leaves2['( abs ` %s )' % IX] = ('RR', w.s([ixc], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A1, IX)))
    fin = linarith(w, A1, [tri2, lre, lim], '( abs ` x ) <_ %s' % RB_, leaves=leaves2)
    ral = w.s([fin], 'ralrimiva', '( %s -> A. x e. %s ( abs ` x ) <_ %s )' % (A0, RECT, RB_))
    ar = w.s([ac], 'recld', '( %s -> %s e. RR )' % (A0, RA)); br = w.s([bc], 'recld', '( %s -> %s e. RR )' % (A0, RB))
    ai = w.s([ac], 'imcld', '( %s -> %s e. RR )' % (A0, IA)); bi = w.s([bc], 'imcld', '( %s -> %s e. RR )' % (A0, IB))
    def absr(X, xr):
        return w.s([w.s([xr], 'recnd', '( %s -> %s e. CC )' % (A0, X))], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, X))
    rbr = w.s([w.s([absr(RA, ar), absr(RB, br)], 'readdcld', '( %s -> %s e. RR )' % (A0, SR)), w.s([absr(IA, ai), absr(IB, bi)], 'readdcld', '( %s -> %s e. RR )' % (A0, SI))], 'readdcld', '( %s -> %s e. RR )' % (A0, RB_))
    sub = w.s([w.s([], 'breq2', '( r = %s -> ( ( abs ` x ) <_ r <-> ( abs ` x ) <_ %s ) )' % (RB_, RB_))], 'ralbidv', '( r = %s -> ( A. x e. %s ( abs ` x ) <_ r <-> A. x e. %s ( abs ` x ) <_ %s ) )' % (RB_, RECT, RECT, RB_))
    bnd = w.s([rbr, ral, w.s([sub], 'rspcev', '( ( %s e. RR /\\ A. x e. %s ( abs ` x ) <_ %s ) -> %s )' % (RB_, RECT, RB_, BND))], 'syl2anc', '( %s -> %s )' % (A0, BND))
    w.qed([w.s([cld, bnd], 'jca', '( %s -> ( %s e. %s /\\ %s ) )' % (A0, RECT, CLS, BND)), hb], 'mpbird', '( %s -> %s e. Comp )' % (A0, JR))
    run1(w)

    # ---- holzfi -------------------------------------------------------------------
    w = W('holzfi', 'Finiteness of the zeros: a holomorphic function on an open set containing the rectangle enlarged by R, not identically zero on the rectangle, has finitely many zeros on the rectangle.')
    A0 = ABNZ
    abg = w.s([], 'simpl', '( %s -> %s )' % (A0, ABGEO))
    nz = w.s([], 'simpr', '( %s -> %s )' % (A0, NZ))
    d = abgeoctx(w, A0, abg)
    NF = '-. %s e. Fin' % ZS
    A1 = '( %s /\\ %s )' % (A0, NF)
    nf = w.s([], 'simpr', '( %s -> %s )' % (A1, NF))
    ej = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
    topt = w.s([w.s([ej], 'cnfldtop', '%s e. Top' % TOP)], 'a1i', '( %s -> %s e. Top )' % (A1, TOP))
    crss = w.s([d['crss']], 'adantr', '( %s -> %s C_ CC )' % (A1, RECT))
    zss = w.s([w.s([], 'ssrab2', '%s C_ %s' % (ZS, RECT))], 'a1i', '( %s -> %s C_ %s )' % (A1, ZS, RECT))
    unic = w.s([], 'unicntop', 'CC = U. %s' % TOP)
    ru = w.s([topt, crss, w.s([unic], 'restuni', '( ( %s e. Top /\\ %s C_ CC ) -> %s = U. %s )' % (TOP, RECT, RECT, JR))], 'syl2anc', '( %s -> %s = U. %s )' % (A1, RECT, JR))
    cmp = w.s([w.s([d['ab']], 'adantr', '( %s -> %s )' % (A1, AB)), w.inst('crectcmp')], 'syl', '( %s -> %s e. Comp )' % (A1, JR))
    zsu = w.s([zss, ru], 'sseqtrd', '( %s -> %s C_ U. %s )' % (A1, ZS, JR))
    LPJ = '( ( limPt ` %s ) ` %s )' % (JR, ZS)
    bw = w.s([cmp, zsu, nf, w.s([w.s([], 'eqid', 'U. %s = U. %s' % (JR, JR))], 'bwth', '( ( %s e. Comp /\\ %s C_ U. %s /\\ %s ) -> E. p e. U. %s p e. %s )' % (JR, ZS, JR, NF, JR, LPJ))], 'syl3anc',
             '( %s -> E. p e. U. %s p e. %s )' % (A1, JR, LPJ))
    exp_ = w.s([bw, w.s([ru], 'rexeqdv', '( %s -> ( E. p e. %s p e. %s <-> E. p e. U. %s p e. %s ) )' % (A1, RECT, LPJ, JR, LPJ))], 'mpbird', '( %s -> E. p e. %s p e. %s )' % (A1, RECT, LPJ))
    A2 = '( %s /\\ ( p e. %s /\\ p e. %s ) )' % (A1, RECT, LPJ)
    pin = w.s([w.s([], 'simpr', '( %s -> ( p e. %s /\\ p e. %s ) )' % (A2, RECT, LPJ)), w.inst('simpl')], 'syl', '( %s -> p e. %s )' % (A2, RECT))
    plp = w.s([w.s([], 'simpr', '( %s -> ( p e. %s /\\ p e. %s ) )' % (A2, RECT, LPJ)), w.inst('simpr')], 'syl', '( %s -> p e. %s )' % (A2, LPJ))
    LPT = '( ( limPt ` %s ) ` %s )' % (TOP, ZS)
    rlp = w.s([w.s([topt], 'adantr', '( %s -> %s e. Top )' % (A2, TOP)), w.s([crss], 'adantr', '( %s -> %s C_ CC )' % (A2, RECT)), w.s([zss], 'adantr', '( %s -> %s C_ %s )' % (A2, ZS, RECT)),
               w.s([unic, w.s([], 'eqid', '%s = %s' % (JR, JR))], 'restlp', '( ( %s e. Top /\\ %s C_ CC /\\ %s C_ %s ) -> %s = ( %s i^i %s ) )' % (TOP, RECT, ZS, RECT, LPJ, LPT, RECT))], 'syl3anc',
              '( %s -> %s = ( %s i^i %s ) )' % (A2, LPJ, LPT, RECT))
    plt = w.s([w.s([w.s([plp, rlp], 'eleqtrd', '( %s -> p e. ( %s i^i %s ) )' % (A2, LPT, RECT)), w.s([], 'elin', '( p e. ( %s i^i %s ) <-> ( p e. %s /\\ p e. %s ) )' % (LPT, RECT, LPT, RECT))], 'sylib', '( %s -> ( p e. %s /\\ p e. %s ) )' % (A2, LPT, RECT)), w.inst('simpl')], 'syl',
              '( %s -> p e. %s )' % (A2, LPT))
    pc = w.s([w.s([crss], 'adantr', '( %s -> %s C_ CC )' % (A2, RECT)), pin], 'sseldd', '( %s -> p e. CC )' % A2)
    zsc = w.s([w.s([zss], 'adantr', '( %s -> %s C_ %s )' % (A2, ZS, RECT)), w.s([crss], 'adantr', '( %s -> %s C_ CC )' % (A2, RECT))], 'sstrd', '( %s -> %s C_ CC )' % (A2, ZS))
    # the local factorisation at p and the isolation of p
    abnz2 = w.s([], 'simpll', '( %s -> %s )' % (A2, ABNZ))
    fac = w.s([abnz2, pin, w.inst('holnfac2')], 'syl2anc', '( %s -> %s )' % (A2, EXFAC('p')))
    A3 = '( ( %s /\\ n e. NN0 ) /\\ %s )' % (A2, PHI('p', 'n'))
    ph3 = w.s([], 'simpr', '( %s -> %s )' % (A3, PHI('p', 'n')))
    gh = w.s([ph3, w.inst('simp1')], 'syl', '( %s -> ( g e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D g ) ) )' % A3)
    nst = w.s([w.s([w.s([w.s([d['ab'], d['Rrp']], 'jca', '( %s -> ( %s /\\ R e. RR+ ) )' % (A0, AB))], 'ad2antrr', '( %s -> ( %s /\\ R e. RR+ ) )' % (A2, AB)), pin], 'jca', '( %s -> ( ( %s /\\ R e. RR+ ) /\\ p e. %s ) )' % (A2, AB, RECT)), w.inst('holnest')], 'syl',
              '( %s -> ( %s /\\ %s ) )' % (A2, INTG(AR, BR, 'p'), RBDG(AR, BR, 'p')))
    pout = w.s([w.s([d['abr']], 'ad2antrr', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A2, AR, BR)), w.s([nst, w.inst('simpl')], 'syl', '( %s -> %s )' % (A2, INTG(AR, BR, 'p'))), w.inst('crectinp')], 'syl2anc', '( %s -> p e. ( %s crect %s ) )' % (A2, AR, BR))
    pd = w.s([w.s([d['nss']], 'ad2antrr', '( %s -> ( %s crect %s ) C_ D )' % (A2, AR, BR)), pout], 'sseldd', '( %s -> p e. D )' % A2)
    gpn = w.s([w.s([gh, w.inst('simpl')], 'syl', '( %s -> g e. ( D -cn-> CC ) )' % A3), w.s([pd], 'ad2antrr', '( %s -> p e. D )' % A3), w.s([ph3, w.inst('simp2')], 'syl', '( %s -> ( g ` p ) =/= 0 )' % A3)], '3jca',
              '( %s -> ( g e. ( D -cn-> CC ) /\\ p e. D /\\ ( g ` p ) =/= 0 ) )' % A3)
    nfac = w.s([w.s([], 'simplr', '( %s -> n e. NN0 )' % A3), w.s([ph3, w.inst('simp3')], 'syl', '( %s -> A. z e. D ( F ` z ) = ( ( ( z - p ) ^ n ) x. ( g ` z ) ) )' % A3)], 'jca',
               '( %s -> ( n e. NN0 /\\ A. z e. D ( F ` z ) = ( ( ( z - p ) ^ n ) x. ( g ` z ) ) ) )' % A3)
    iso3 = w.s([gpn, nfac, w.inst('holzisol')], 'syl2anc', '( %s -> E. d e. RR+ %s )' % (A3, ISO('p', 'd')))
    ex1 = w.s([w.s([iso3], 'ex', '( ( %s /\\ n e. NN0 ) -> ( %s -> E. d e. RR+ %s ) )' % (A2, PHI('p', 'n'), ISO('p', 'd')))], 'exlimdv', '( ( %s /\\ n e. NN0 ) -> ( E. g %s -> E. d e. RR+ %s ) )' % (A2, PHI('p', 'n'), ISO('p', 'd')))
    iso = w.s([fac, w.s([ex1], 'rexlimdva', '( %s -> ( %s -> E. d e. RR+ %s ) )' % (A2, EXFAC('p'), ISO('p', 'd')))], 'mpd', '( %s -> E. d e. RR+ %s )' % (A2, ISO('p', 'd')))
    # contradiction with the limit point
    A4 = '( %s /\\ ( d e. RR+ /\\ %s ) )' % (A2, ISO('p', 'd'))
    drp = w.s([w.s([], 'simpr', '( %s -> ( d e. RR+ /\\ %s ) )' % (A4, ISO('p', 'd'))), w.inst('simpl')], 'syl', '( %s -> d e. RR+ )' % A4)
    isod = w.s([w.s([], 'simpr', '( %s -> ( d e. RR+ /\\ %s ) )' % (A4, ISO('p', 'd'))), w.inst('simpr')], 'syl', '( %s -> %s )' % (A4, ISO('p', 'd')))
    ABSM = '( abs o. - )'
    BL = '( p ( ball ` %s ) d )' % ABSM
    xm4 = closed(w, A4, 'cnxmet', '%s e. ( *Met ` CC )' % ABSM)
    jm = w.s([ej], 'cnfldtopn', '%s = ( MetOpen ` %s )' % (TOP, ABSM))
    pc4 = w.s([pc], 'adantr', '( %s -> p e. CC )' % A4)
    dxr = w.s([drp], 'rpxrd', '( %s -> d e. RR* )' % A4)
    bopn = w.s([xm4, pc4, dxr, w.s([jm], 'blopn', '( ( %s e. ( *Met ` CC ) /\\ p e. CC /\\ d e. RR* ) -> %s e. %s )' % (ABSM, BL, TOP))], 'syl3anc', '( %s -> %s e. %s )' % (A4, BL, TOP))
    pinb = w.s([xm4, pc4, drp, w.inst('blcntr')], 'syl3anc', '( %s -> p e. %s )' % (A4, BL))
    NB = '( %s i^i ( %s \\ { p } ) ) =/= (/)' % (BL, ZS)
    ALLX = 'A. x e. %s ( p e. x -> ( x i^i ( %s \\ { p } ) ) =/= (/) )' % (TOP, ZS)
    lp3 = w.s([w.s([topt], 'ad2antrr', '( %s -> %s e. Top )' % (A4, TOP)), w.s([zsc], 'adantr', '( %s -> %s C_ CC )' % (A4, ZS)), pc4, w.s([unic], 'islp3', '( ( %s e. Top /\\ %s C_ CC /\\ p e. CC ) -> ( p e. %s <-> %s ) )' % (TOP, ZS, LPT, ALLX))], 'syl3anc',
               '( %s -> ( p e. %s <-> %s ) )' % (A4, LPT, ALLX))
    allx = w.s([w.s([plt], 'adantr', '( %s -> p e. %s )' % (A4, LPT)), lp3], 'mpbid', '( %s -> %s )' % (A4, ALLX))
    xsub = w.s([w.s([], 'eleq2', '( x = %s -> ( p e. x <-> p e. %s ) )' % (BL, BL)), w.s([w.s([], 'ineq1', '( x = %s -> ( x i^i ( %s \\ { p } ) ) = ( %s i^i ( %s \\ { p } ) ) )' % (BL, ZS, BL, ZS))], 'neeq1d', '( x = %s -> ( ( x i^i ( %s \\ { p } ) ) =/= (/) <-> %s ) )' % (BL, ZS, NB))], 'imbi12d',
               '( x = %s -> ( ( p e. x -> ( x i^i ( %s \\ { p } ) ) =/= (/) ) <-> ( p e. %s -> %s ) ) )' % (BL, ZS, BL, NB))
    nb = w.s([pinb, w.s([xsub, allx, bopn], 'rspcdva', '( %s -> ( p e. %s -> %s ) )' % (A4, BL, NB))], 'mpd', '( %s -> %s )' % (A4, NB))
    exq = w.s([nb, w.s([], 'n0', '( %s <-> E. q q e. ( %s i^i ( %s \\ { p } ) ) )' % (NB, BL, ZS))], 'sylib', '( %s -> E. q q e. ( %s i^i ( %s \\ { p } ) ) )' % (A4, BL, ZS))
    A5 = '( %s /\\ q e. ( %s i^i ( %s \\ { p } ) ) )' % (A4, BL, ZS)
    qboth = w.s([w.s([], 'simpr', '( %s -> q e. ( %s i^i ( %s \\ { p } ) ) )' % (A5, BL, ZS)), w.s([], 'elin', '( q e. ( %s i^i ( %s \\ { p } ) ) <-> ( q e. %s /\\ q e. ( %s \\ { p } ) ) )' % (BL, ZS, BL, ZS))], 'sylib', '( %s -> ( q e. %s /\\ q e. ( %s \\ { p } ) ) )' % (A5, BL, ZS))
    qbl = w.s([qboth, w.inst('simpl')], 'syl', '( %s -> q e. %s )' % (A5, BL))
    qdif = w.s([w.s([qboth, w.inst('simpr')], 'syl', '( %s -> q e. ( %s \\ { p } ) )' % (A5, ZS)), w.s([], 'eldifsn', '( q e. ( %s \\ { p } ) <-> ( q e. %s /\\ q =/= p ) )' % (ZS, ZS))], 'sylib', '( %s -> ( q e. %s /\\ q =/= p ) )' % (A5, ZS))
    qzs = w.s([qdif, w.inst('simpl')], 'syl', '( %s -> q e. %s )' % (A5, ZS))
    qne = w.s([qdif, w.inst('simpr')], 'syl', '( %s -> q =/= p )' % A5)
    qr = w.s([qzs, w.s([w.s([w.s([], 'fveq2', '( r = q -> ( F ` r ) = ( F ` q ) )')], 'eqeq1d', '( r = q -> ( ( F ` r ) = 0 <-> ( F ` q ) = 0 ) )')], 'elrab', '( q e. %s <-> ( q e. %s /\\ ( F ` q ) = 0 ) )' % (ZS, RECT))], 'sylib',
             '( %s -> ( q e. %s /\\ ( F ` q ) = 0 ) )' % (A5, RECT))
    qin = w.s([qr, w.inst('simpl')], 'syl', '( %s -> q e. %s )' % (A5, RECT))
    fq0 = w.s([qr, w.inst('simpr')], 'syl', '( %s -> ( F ` q ) = 0 )' % A5)
    qc = w.s([w.s([crss], 'ad3antrrr', '( %s -> %s C_ CC )' % (A5, RECT)), qin], 'sseldd', '( %s -> q e. CC )' % A5)
    pc5 = w.s([pc4], 'adantr', '( %s -> p e. CC )' % A5)
    bl2 = w.s([w.s([w.s([xm4], 'adantr', '( %s -> %s e. ( *Met ` CC ) )' % (A5, ABSM)), w.s([dxr], 'adantr', '( %s -> d e. RR* )' % A5)], 'jca', '( %s -> ( %s e. ( *Met ` CC ) /\\ d e. RR* ) )' % (A5, ABSM)), w.s([pc5, qc], 'jca', '( %s -> ( p e. CC /\\ q e. CC ) )' % A5), w.inst('elbl2')], 'syl2anc',
              '( %s -> ( q e. %s <-> ( p %s q ) < d ) )' % (A5, BL, ABSM))
    dlt = w.s([qbl, bl2], 'mpbid', '( %s -> ( p %s q ) < d )' % (A5, ABSM))
    dv = w.s([pc5, qc, w.s([w.s([], 'eqid', '%s = %s' % (ABSM, ABSM))], 'cnmetdval', '( ( p e. CC /\\ q e. CC ) -> ( p %s q ) = ( abs ` ( p - q ) ) )' % ABSM)], 'syl2anc', '( %s -> ( p %s q ) = ( abs ` ( p - q ) ) )' % (A5, ABSM))
    dv2 = w.s([dv, w.s([pc5, qc, w.inst('abssub')], 'syl2anc', '( %s -> ( abs ` ( p - q ) ) = ( abs ` ( q - p ) ) )' % A5)], 'eqtrd', '( %s -> ( p %s q ) = ( abs ` ( q - p ) ) )' % (A5, ABSM))
    qlt = w.s([dv2, dlt], 'eqbrtrrd', '( %s -> ( abs ` ( q - p ) ) < d )' % A5)
    nstq = w.s([w.s([w.s([w.s([d['ab'], d['Rrp']], 'jca', '( %s -> ( %s /\\ R e. RR+ ) )' % (A0, AB))], 'ad4antr', '( %s -> ( %s /\\ R e. RR+ ) )' % (A5, AB)), qin], 'jca', '( %s -> ( ( %s /\\ R e. RR+ ) /\\ q e. %s ) )' % (A5, AB, RECT)), w.inst('holnest')], 'syl',
               '( %s -> ( %s /\\ %s ) )' % (A5, INTG(AR, BR, 'q'), RBDG(AR, BR, 'q')))
    qout = w.s([w.s([d['abr']], 'ad4antr', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A5, AR, BR)), w.s([nstq, w.inst('simpl')], 'syl', '( %s -> %s )' % (A5, INTG(AR, BR, 'q'))), w.inst('crectinp')], 'syl2anc', '( %s -> q e. ( %s crect %s ) )' % (A5, AR, BR))
    qD = w.s([w.s([d['nss']], 'ad4antr', '( %s -> ( %s crect %s ) C_ D )' % (A5, AR, BR)), qout], 'sseldd', '( %s -> q e. D )' % A5)
    zsub = w.s([w.s([w.s([], 'neeq1', '( z = q -> ( z =/= p <-> q =/= p ) )'), w.s([w.s([w.s([], 'oveq1', '( z = q -> ( z - p ) = ( q - p ) )')], 'fveq2d', '( z = q -> ( abs ` ( z - p ) ) = ( abs ` ( q - p ) ) )')], 'breq1d', '( z = q -> ( ( abs ` ( z - p ) ) < d <-> ( abs ` ( q - p ) ) < d ) )')], 'anbi12d',
                    '( z = q -> ( ( z =/= p /\\ ( abs ` ( z - p ) ) < d ) <-> ( q =/= p /\\ ( abs ` ( q - p ) ) < d ) ) )'),
               w.s([w.s([], 'fveq2', '( z = q -> ( F ` z ) = ( F ` q ) )')], 'neeq1d', '( z = q -> ( ( F ` z ) =/= 0 <-> ( F ` q ) =/= 0 ) )')], 'imbi12d',
              '( z = q -> ( ( ( z =/= p /\\ ( abs ` ( z - p ) ) < d ) -> ( F ` z ) =/= 0 ) <-> ( ( q =/= p /\\ ( abs ` ( q - p ) ) < d ) -> ( F ` q ) =/= 0 ) ) )')
    fqne = w.s([w.s([qne, qlt], 'jca', '( %s -> ( q =/= p /\\ ( abs ` ( q - p ) ) < d ) )' % A5), w.s([zsub, w.s([isod], 'adantr', '( %s -> %s )' % (A5, ISO('p', 'd'))), qD], 'rspcdva', '( %s -> ( ( q =/= p /\\ ( abs ` ( q - p ) ) < d ) -> ( F ` q ) =/= 0 ) )' % A5)], 'mpd',
               '( %s -> ( F ` q ) =/= 0 )' % A5)
    f5 = w.s([fqne, fq0], 'pm2.21ddne', '( %s -> F. )' % A5)
    f4 = w.s([exq, f5], 'exlimddv', '( %s -> F. )' % A4)
    f2 = w.s([iso, f4], 'rexlimddv', '( %s -> F. )' % A2)
    f1 = w.s([exp_, f2], 'rexlimddv', '( %s -> F. )' % A1)
    w.qed([w.s([f1], 'inegd', '( %s -> -. %s )' % (A0, NF))], 'notnotrd', '( %s -> %s e. Fin )' % (A0, ZS))
    run1(w)
