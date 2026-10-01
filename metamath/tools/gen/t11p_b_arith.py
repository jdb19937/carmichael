"""T11 helper (pool): the list arithmetic the pool loop reads at one entry and in the sum.

  tmipzk   one entry of the kept list: the reversed pool of the first ` j + 1 ` divisors is the entry ` p = d k + 1 `
           pushed on that of the first ` j ` when ` p ` is kept, unchanged otherwise; the charge of the entry is Lean's
           ` pgc x z k d ` (Steps23.lean ` poolGo_append ` , ` poolGo_single ` )
  tmipzs   the charges of the entries sum to the cost of the pool (telescoped)

    MM_DB=sorties/t11p.mm python3 tools/gen/t11p_b_arith.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from a4alib import *
from lin import linarith, lineq
from cl import Closure
import t6blib
import t11_g_parith as GP
from t11_g_parith import pg_cases, PG, P1, P2, FZG, WN
t6blib._STMT.update(GP.STMTS)

SEL = sys.argv[1:]

DJ = '( L ` J )'
PPJ = '( ( %s x. G ) + 1 )' % DJ
CONDJ = '( %s <_ F /\\ Z < %s )' % (PPJ, PPJ)
PRIMEJ = '( 1st ` ( IsPrimeTD ` %s ) ) = 1o' % PPJ
IP2J = '( 2nd ` ( IsPrimeTD ` %s ) )' % PPJ
RV = lambda k: '( reverse ` %s )' % P1('( L prefix %s )' % k)
ENCL_ = lambda V, X: '( ( encList ` %s ) ++ %s )' % (V, X)
EW_ = lambda t, X: '( ( encNatGam ` %s ) ++ ( <" 4 "> ++ %s ) )' % (t, X)
HK = "( ( %s /\\ L e. Word NN0 ) /\\ ( J e. ( 0 ..^ ( # ` L ) ) /\\ Z' e. Word Gamma' ) )" % FZG
C0K = ENCL_(RV('J'), "Z'")
EQK1 = '%s = if ( ( %s /\\ %s ) , %s , %s )' % (ENCL_(RV('( J + 1 )'), "Z'"), CONDJ, PRIMEJ, EW_(PPJ, C0K), C0K)
EQK2 = '%s = if ( %s , ( %s + 1 ) , 1 )' % (P2('<" %s ">' % DJ), CONDJ, IP2J)
ST_K = '( %s -> ( %s /\\ %s ) )' % (HK, EQK1, EQK2)
HS = '( %s /\\ L e. Word NN0 )' % FZG
ST_S = '( %s -> sum_ j e. ( 0 ..^ ( # ` L ) ) %s = %s )' % (HS, P2('<" ( L ` j ) ">'), P2('L'))
STMTS = {'tmipzk': ST_K, 'tmipzs': ST_S}


def tmipzk():
    w = W('tmipzk', 'One entry of Lean\'s ` poolGo ` at a prefix (Steps23.lean ` poolGo_append ` , ` poolGo_single ` ): the reversed '
                    'pool of the first ` j + 1 ` divisors, encoded over ` Z\' ` , is ` p = d k + 1 ` pushed on that of the first ` j ` '
                    'when ` p <_ x , z < p ` and ` p ` is prime, unchanged otherwise; the cost of the entry is ` pgc x z k d ` .')
    s = w.s
    A = HK
    fzg = s([], 'simpll', '( %s -> %s )' % (A, FZG))
    lw = s([], 'simplr', '( %s -> L e. Word NN0 )' % A)
    jj = s([], 'simprl', '( %s -> J e. ( 0 ..^ ( # ` L ) ) )' % A)
    zw = s([], 'simprr', "( %s -> Z' e. Word Gamma' )" % A)
    dn = s([lw, jj, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (A, DJ))
    P0_, P1_ = '( L prefix J )', '( L prefix ( J + 1 ) )'
    S1 = '<" %s ">' % DJ
    p0w = s([lw, w.inst('pfxcl')], 'syl', '( %s -> %s e. Word NN0 )' % (A, P0_))
    s1w = s([dn, w.inst('s1cl')], 'syl', '( %s -> %s e. Word NN0 )' % (A, S1))
    pf = s([lw, jj, w.inst('tm2lpfxs1')], 'syl2anc', '( %s -> %s = ( %s ++ %s ) )' % (A, P1_, P0_, S1))
    app = s([s([s([fzg, s1w], 'jca', '( %s -> ( %s /\\ %s e. Word NN0 ) )' % (A, FZG, S1)), p0w], 'jca',
               '( %s -> ( ( %s /\\ %s e. Word NN0 ) /\\ %s e. Word NN0 ) )' % (A, FZG, S1, P0_)), w.inst('tmpgapp')], 'syl',
            '( %s -> %s = <. ( %s ++ %s ) , ( %s + %s ) >. )' % (A, PG('( %s ++ %s )' % (P0_, S1)), P1(P0_), P1(S1), P2(P0_), P2(S1)))
    e1 = s([s([pf], 'fveq2d', '( %s -> %s = %s )' % (A, PG(P1_), PG('( %s ++ %s )' % (P0_, S1)))), app], 'eqtrd',
           '( %s -> %s = <. ( %s ++ %s ) , ( %s + %s ) >. )' % (A, PG(P1_), P1(P0_), P1(S1), P2(P0_), P2(S1)))
    cl0 = s([s([fzg, p0w], 'jca', '( %s -> ( %s /\\ %s e. Word NN0 ) )' % (A, FZG, P0_)), w.inst('poolgocl')], 'syl', '( %s -> %s e. %s )' % (A, PG(P0_), WN))
    cls = s([s([fzg, s1w], 'jca', '( %s -> ( %s /\\ %s e. Word NN0 ) )' % (A, FZG, S1)), w.inst('poolgocl')], 'syl', '( %s -> %s e. %s )' % (A, PG(S1), WN))
    a0, b0 = paircl(w, A, PG(P0_), cl0, 'Word NN0', 'NN0')
    a1, b1 = paircl(w, A, PG(S1), cls, 'Word NN0', 'NN0')
    X1 = '( %s ++ %s )' % (P1(P0_), P1(S1))
    X2 = '( %s + %s )' % (P2(P0_), P2(S1))
    x1v = s([s([a0, a1, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word NN0 )' % (A, X1))], 'elexd', '( %s -> %s e. _V )' % (A, X1))
    x2v = s([s([b0, b1], 'nn0addcld', '( %s -> %s e. NN0 )' % (A, X2))], 'elexd', '( %s -> %s e. _V )' % (A, X2))
    f1 = projeq(w, A, PG(P1_), e1, X1, X2, x1v, x2v, 1)
    # reverse
    r1 = s([s([f1], 'fveq2d', '( %s -> %s = ( reverse ` %s ) )' % (A, RV('( J + 1 )'), X1)),
            s([a0, a1, w.inst('revccat')], 'syl2anc', '( %s -> ( reverse ` %s ) = ( ( reverse ` %s ) ++ %s ) )' % (A, X1, P1(S1), RV('J')))],
           'eqtrd', '( %s -> %s = ( ( reverse ` %s ) ++ %s ) )' % (A, RV('( J + 1 )'), P1(S1), RV('J')))
    rvw = s([a0, w.inst('revcl')], 'syl', '( %s -> %s e. Word NN0 )' % (A, RV('J')))
    # the singleton, by cases ( <" d "> ++ (/) = <" d "> )
    e0 = s([s([], 'wrd0', '(/) e. Word NN0')], 'a1i', '( %s -> (/) e. Word NN0 )' % A)
    # pg_cases is stated at the letter P: substitute by hand through its own statement text
    PS = '( <" %s "> ++ (/) )' % DJ
    rid = s([s1w, w.inst('ccatrid')], 'syl', '( %s -> %s = %s )' % (A, PS, S1))
    gsd = s([s([rid], 'fveq2d', '( %s -> %s = %s )' % (A, PG(PS), PG(S1)))], 'eqcomd', '( %s -> %s = %s )' % (A, PG(S1), PG(PS)))
    cs_ = s([s([fzg, dn], 'jca', '( %s -> ( %s /\\ %s e. NN0 ) )' % (A, FZG, DJ)), e0, w.inst('poolgocs')], 'syl2anc',
            '( %s -> %s = if ( %s , <. if ( %s , ( <" %s "> ++ %s ) , %s ) , ( ( %s + %s ) + 1 ) >. , <. %s , ( %s + 1 ) >. ) )'
            % (A, PG(PS), CONDJ, PRIMEJ, PPJ, P1('(/)'), P1('(/)'), P2('(/)'), IP2J, P1('(/)'), P2('(/)')))
    p0 = s([fzg, w.inst('poolgo0')], 'syl', '( %s -> %s = <. (/) , 0 >. )' % (A, PG('(/)')))
    z = s([s([], '0ex', '(/) e. _V')], 'a1i', '( %s -> (/) e. _V )' % A)
    z2 = s([s([], 'c0ex', '0 e. _V')], 'a1i', '( %s -> 0 e. _V )' % A)
    q1 = projeq(w, A, PG('(/)'), p0, '(/)', '0', z, z2, 1)
    q2 = projeq(w, A, PG('(/)'), p0, '(/)', '0', z, z2, 2)
    rr, x = w.rewrite(PG(PS) if False else 'if ( %s , <. if ( %s , ( <" %s "> ++ %s ) , %s ) , ( ( %s + %s ) + 1 ) >. , <. %s , ( %s + 1 ) >. )'
                      % (CONDJ, PRIMEJ, PPJ, P1('(/)'), P1('(/)'), P2('(/)'), IP2J, P1('(/)'), P2('(/)')),
                      {P1('(/)'): ('(/)', q1), P2('(/)'): ('0', q2)}, A)
    pp = s([s([dn, s([fzg], 'simprd', '( %s -> G e. NN0 )' % A)], 'nn0mulcld', '( %s -> ( %s x. G ) e. NN0 )' % (A, DJ)), w.inst('peano2nn0')], 'syl',
           '( %s -> %s e. NN0 )' % (A, PPJ))
    ipc = s([pp, w.inst('isprimetdcl')], 'syl', '( %s -> ( IsPrimeTD ` %s ) e. ( 2o X. NN0 ) )' % (A, PPJ))
    ip2 = s([ipc, w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (A, IP2J))
    ipc_ = s([ip2], 'nn0cnd', '( %s -> %s e. CC )' % (A, IP2J))
    a0e = s([ipc_], 'addlidd', '( %s -> ( 0 + %s ) = %s )' % (A, IP2J, IP2J))
    ppw = s([pp, w.inst('s1cl')], 'syl', '( %s -> <" %s "> e. Word NN0 )' % (A, PPJ))
    prid = s([ppw, w.inst('ccatrid')], 'syl', '( %s -> ( <" %s "> ++ (/) ) = <" %s "> )' % (A, PPJ, PPJ))
    rr2, x2 = w.rewrite(x, {'( <" %s "> ++ (/) )' % PPJ: ('<" %s ">' % PPJ, prid), '( 0 + %s )' % IP2J: (IP2J, a0e),
                            '( 0 + 1 )': ('1', s([s([], '0p1e1', '( 0 + 1 ) = 1')], 'a1i', '( %s -> ( 0 + 1 ) = 1 )' % A))}, A)
    SV = 'if ( %s , <. if ( %s , <" %s "> , (/) ) , ( %s + 1 ) >. , <. (/) , 1 >. )' % (CONDJ, PRIMEJ, PPJ, IP2J)
    assert x2 == SV, x2
    sv = s([s([s([gsd, cs_], 'eqtrd', '( %s -> %s = %s )' % (A, PG(S1), cs_ and 'if ( %s , <. if ( %s , ( <" %s "> ++ %s ) , %s ) , ( ( %s + %s ) + 1 ) >. , <. %s , ( %s + 1 ) >. )'
                                                               % (CONDJ, PRIMEJ, PPJ, P1('(/)'), P1('(/)'), P2('(/)'), IP2J, P1('(/)'), P2('(/)')))), rr], 'eqtrd',
               '( %s -> %s = %s )' % (A, PG(S1), x)), rr2], 'eqtrd', '( %s -> %s = %s )' % (A, PG(S1), SV))
    # cases
    AT = '( %s /\\ %s )' % (A, CONDJ)
    AF = '( %s /\\ -. %s )' % (A, CONDJ)
    ct, cf_ = ifproj(w, A, PG(S1), sv, CONDJ, '<. if ( %s , <" %s "> , (/) ) , ( %s + 1 ) >.' % (PRIMEJ, PPJ, IP2J), '<. (/) , 1 >.')
    L_ = lambda ph2, st, f: s([st], 'adantr', '( %s -> %s )' % (ph2, f))
    IFE = 'if ( %s , <" %s "> , (/) )' % (PRIMEJ, PPJ)
    ifw = s([s([ppw, s([s([], 'wrd0', '(/) e. Word NN0')], 'a1i', '( %s -> (/) e. Word NN0 )' % A)], 'ifcld',
               '( %s -> %s e. Word NN0 )' % (A, IFE))], 'elexd', '( %s -> %s e. _V )' % (A, IFE))
    i1v = s([s([ip2, w.inst('peano2nn0')], 'syl', '( %s -> ( %s + 1 ) e. NN0 )' % (A, IP2J))], 'elexd', '( %s -> ( %s + 1 ) e. _V )' % (A, IP2J))
    t1 = projeq(w, AT, PG(S1), ct, IFE, '( %s + 1 )' % IP2J, L_(AT, ifw, '%s e. _V' % IFE), L_(AT, i1v, '( %s + 1 ) e. _V' % IP2J), 1)
    t2 = projeq(w, AT, PG(S1), ct, IFE, '( %s + 1 )' % IP2J, L_(AT, ifw, '%s e. _V' % IFE), L_(AT, i1v, '( %s + 1 ) e. _V' % IP2J), 2)
    zv = s([s([], '0ex', '(/) e. _V')], 'a1i', '( %s -> (/) e. _V )' % AF)
    ov = s([s([], '1ex', '1 e. _V')], 'a1i', '( %s -> 1 e. _V )' % AF)
    f1_ = projeq(w, AF, PG(S1), cf_, '(/)', '1', zv, ov, 1)
    f2_ = projeq(w, AF, PG(S1), cf_, '(/)', '1', zv, ov, 2)
    IFC = 'if ( %s , ( %s + 1 ) , 1 )' % (CONDJ, IP2J)
    ch_t = s([t2, s([s([], 'simpr', '( %s -> %s )' % (AT, CONDJ))], 'iftrued', '( %s -> %s = ( %s + 1 ) )' % (AT, IFC, IP2J))], 'eqtr4d',
             '( %s -> %s )' % (AT, EQK2))
    ch_f = s([f2_, s([s([], 'simpr', '( %s -> -. %s )' % (AF, CONDJ))], 'iffalsed', '( %s -> %s = 1 )' % (AF, IFC))], 'eqtr4d', '( %s -> %s )' % (AF, EQK2))
    ch = s([ch_t, ch_f], 'pm2.61dan', '( %s -> %s )' % (A, EQK2))
    # the encoded open list
    KP = '( %s /\\ %s )' % (CONDJ, PRIMEJ)
    IFK = 'if ( %s , %s , %s )' % (KP, EW_(PPJ, C0K), C0K)
    ELR = '( encList ` %s )' % RV('J')
    EGA = '( encNatGam ` %s )' % PPJ

    def enc_eq(ph2, s1eq, keep):
        """( ph2 -> ENCL( RV( J + 1 ) , Z' ) = value ) from s1eq : ( ph2 -> ( 1st ` PG( S1 ) ) = <" p "> | (/) )"""
        Lf = lambda st, f: GP.lift(w, ph2, A, st) if ph2 != A else st
        rr1 = Lf(r1, '%s = ( ( reverse ` %s ) ++ %s )' % (RV('( J + 1 )'), P1(S1), RV('J')))
        if keep:
            V1 = '<" %s ">' % PPJ
            rv1 = s([s([s1eq], 'fveq2d', '( %s -> ( reverse ` %s ) = ( reverse ` %s ) )' % (ph2, P1(S1), V1)),
                     s([s([], 'revs1', '( reverse ` %s ) = %s' % (V1, V1))], 'a1i', '( %s -> ( reverse ` %s ) = %s )' % (ph2, V1, V1))], 'eqtrd',
                    '( %s -> ( reverse ` %s ) = %s )' % (ph2, P1(S1), V1))
            r2_ = s([rr1, s([rv1], 'oveq1d', '( %s -> ( ( reverse ` %s ) ++ %s ) = ( %s ++ %s ) )' % (ph2, P1(S1), RV('J'), V1, RV('J')))], 'eqtrd',
                    '( %s -> %s = ( %s ++ %s ) )' % (ph2, RV('( J + 1 )'), V1, RV('J')))
            ec = s([Lf(pp, '%s e. NN0' % PPJ), Lf(rvw, '%s e. Word NN0' % RV('J')), w.inst('tm2lenccons')], 'syl2anc',
                   '( %s -> ( encList ` ( %s ++ %s ) ) = ( %s ++ ( <" 4 "> ++ %s ) ) )' % (ph2, V1, RV('J'), EGA, ELR))
            el = s([s([r2_], 'fveq2d', '( %s -> ( encList ` %s ) = ( encList ` ( %s ++ %s ) ) )' % (ph2, RV('( J + 1 )'), V1, RV('J'))), ec], 'eqtrd',
                   '( %s -> ( encList ` %s ) = ( %s ++ ( <" 4 "> ++ %s ) ) )' % (ph2, RV('( J + 1 )'), EGA, ELR))
            ega = s([Lf(pp, '%s e. NN0' % PPJ), w.inst('encnatgamcl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph2, EGA))
            elr = s([Lf(rvw, '%s e. Word NN0' % RV('J')), w.inst('tm2lenccl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph2, ELR))
            s4 = s([s([s([], 'gamma4', "4 e. Gamma'")], 'a1i', "( %s -> 4 e. Gamma' )" % ph2)], 's1cld', "( %s -> <\" 4 \"> e. Word Gamma' )" % ph2)
            g4 = s([s4, elr, w.inst('ccatcl')], 'syl2anc', "( %s -> ( <\" 4 \"> ++ %s ) e. Word Gamma' )" % (ph2, ELR))
            zz = Lf(zw, "Z' e. Word Gamma'")
            a1_ = s([ega, g4, zz, w.inst('ccatass')], 'syl3anc',
                    "( %s -> ( ( %s ++ ( <\" 4 \"> ++ %s ) ) ++ Z' ) = ( %s ++ ( ( <\" 4 \"> ++ %s ) ++ Z' ) ) )" % (ph2, EGA, ELR, EGA, ELR))
            a2_ = s([s4, elr, zz, w.inst('ccatass')], 'syl3anc', "( %s -> ( ( <\" 4 \"> ++ %s ) ++ Z' ) = ( <\" 4 \"> ++ ( %s ++ Z' ) ) )" % (ph2, ELR, ELR))
            t1_ = s([s([el], 'oveq1d', "( %s -> %s = ( ( %s ++ ( <\" 4 \"> ++ %s ) ) ++ Z' ) )" % (ph2, ENCL_(RV('( J + 1 )'), "Z'"), EGA, ELR)), a1_],
                    'eqtrd', "( %s -> %s = ( %s ++ ( ( <\" 4 \"> ++ %s ) ++ Z' ) ) )" % (ph2, ENCL_(RV('( J + 1 )'), "Z'"), EGA, ELR))
            return s([t1_, s([a2_], 'oveq2d', "( %s -> ( %s ++ ( ( <\" 4 \"> ++ %s ) ++ Z' ) ) = %s )" % (ph2, EGA, ELR, EW_(PPJ, C0K)))], 'eqtrd',
                     '( %s -> %s = %s )' % (ph2, ENCL_(RV('( J + 1 )'), "Z'"), EW_(PPJ, C0K)))
        rv1 = s([s([s1eq], 'fveq2d', '( %s -> ( reverse ` %s ) = ( reverse ` (/) ) )' % (ph2, P1(S1))),
                 s([s([], 'rev0', '( reverse ` (/) ) = (/)')], 'a1i', '( %s -> ( reverse ` (/) ) = (/) )' % ph2)], 'eqtrd',
                '( %s -> ( reverse ` %s ) = (/) )' % (ph2, P1(S1)))
        r2_ = s([rr1, s([rv1], 'oveq1d', '( %s -> ( ( reverse ` %s ) ++ %s ) = ( (/) ++ %s ) )' % (ph2, P1(S1), RV('J'), RV('J')))], 'eqtrd',
                '( %s -> %s = ( (/) ++ %s ) )' % (ph2, RV('( J + 1 )'), RV('J')))
        r3_ = s([r2_, s([Lf(rvw, '%s e. Word NN0' % RV('J')), w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ %s ) = %s )' % (ph2, RV('J'), RV('J')))], 'eqtrd',
                '( %s -> %s = %s )' % (ph2, RV('( J + 1 )'), RV('J')))
        return s([s([r3_], 'fveq2d', '( %s -> ( encList ` %s ) = %s )' % (ph2, RV('( J + 1 )'), ELR))], 'oveq1d',
                 '( %s -> %s = %s )' % (ph2, ENCL_(RV('( J + 1 )'), "Z'"), C0K))
    # AT /\ PRIME
    ATP = '( %s /\\ %s )' % (AT, PRIMEJ)
    ATN = '( %s /\\ -. %s )' % (AT, PRIMEJ)
    t1p = s([s([t1], 'adantr', '( %s -> %s = %s )' % (ATP, P1(S1), IFE)), s([s([], 'simpr', '( %s -> %s )' % (ATP, PRIMEJ))], 'iftrued',
                                                                              '( %s -> %s = <" %s "> )' % (ATP, IFE, PPJ))], 'eqtrd',
              '( %s -> %s = <" %s "> )' % (ATP, P1(S1), PPJ))
    kp_ = s([s([s([], 'simplr', '( %s -> %s )' % (ATP, CONDJ)), s([], 'simpr', '( %s -> %s )' % (ATP, PRIMEJ))], 'jca', '( %s -> %s )' % (ATP, KP))],
            'iftrued', '( %s -> %s = %s )' % (ATP, IFK, EW_(PPJ, C0K)))
    ep = s([enc_eq(ATP, t1p, True), kp_], 'eqtr4d', '( %s -> %s )' % (ATP, EQK1))
    t1n = s([s([t1], 'adantr', '( %s -> %s = %s )' % (ATN, P1(S1), IFE)), s([s([], 'simpr', '( %s -> -. %s )' % (ATN, PRIMEJ))], 'iffalsed',
                                                                              '( %s -> %s = (/) )' % (ATN, IFE))], 'eqtrd', '( %s -> %s = (/) )' % (ATN, P1(S1)))
    kn_ = s([s([s([], 'simpr', '( %s -> -. %s )' % (ATN, PRIMEJ))], 'intnand', '( %s -> -. %s )' % (ATN, KP))], 'iffalsed',
            '( %s -> %s = %s )' % (ATN, IFK, C0K))
    en = s([enc_eq(ATN, t1n, False), kn_], 'eqtr4d', '( %s -> %s )' % (ATN, EQK1))
    et = s([ep, en], 'pm2.61dan', '( %s -> %s )' % (AT, EQK1))
    kf_ = s([s([s([], 'simpr', '( %s -> -. %s )' % (AF, CONDJ))], 'intnanrd', '( %s -> -. %s )' % (AF, KP))], 'iffalsed',
            '( %s -> %s = %s )' % (AF, IFK, C0K))
    ef = s([enc_eq(AF, f1_, False), kf_], 'eqtr4d', '( %s -> %s )' % (AF, EQK1))
    ek = s([et, ef], 'pm2.61dan', '( %s -> %s )' % (A, EQK1))
    w.qed([ek, ch], 'jca', ST_K)
    return w.run()


def tmipzs():
    w = W('tmipzs', 'The charges of the entries of Lean\'s ` poolGo ` sum to its cost: ` sum_ j pgc x z k l[j] = ( poolGo x z k l ).2 ` '
                    '(Steps23.lean ` poolGo_append ` at every prefix, telescoped by ~ telfsumo2 ).')
    s = w.s
    A = HS
    fzg = s([], 'simpl', '( %s -> %s )' % (A, FZG))
    lw = s([], 'simpr', '( %s -> L e. Word NN0 )' % A)
    NLW = '( # ` L )'
    pj = '( %s /\\ j e. ( 0 ..^ %s ) )' % (A, NLW)
    jj = s([], 'simpr', '( %s -> j e. ( 0 ..^ %s ) )' % (pj, NLW))
    fz = s([], 'simpll' if False else 'simpl', '( %s -> %s )' % (pj, A))
    fzj = s([fz], 'simpld', '( %s -> %s )' % (pj, FZG))
    lwj = s([fz], 'simprd', '( %s -> L e. Word NN0 )' % pj)
    D_ = '( L ` j )'
    S1 = '<" %s ">' % D_
    P0_, P1_ = '( L prefix j )', '( L prefix ( j + 1 ) )'
    dn = s([lwj, jj, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (pj, D_))
    s1w = s([dn, w.inst('s1cl')], 'syl', '( %s -> %s e. Word NN0 )' % (pj, S1))
    p0w = s([lwj, w.inst('pfxcl')], 'syl', '( %s -> %s e. Word NN0 )' % (pj, P0_))
    pf = s([lwj, jj, w.inst('tm2lpfxs1')], 'syl2anc', '( %s -> %s = ( %s ++ %s ) )' % (pj, P1_, P0_, S1))
    app = s([s([s([fzj, s1w], 'jca', '( %s -> ( %s /\\ %s e. Word NN0 ) )' % (pj, FZG, S1)), p0w], 'jca',
               '( %s -> ( ( %s /\\ %s e. Word NN0 ) /\\ %s e. Word NN0 ) )' % (pj, FZG, S1, P0_)), w.inst('tmpgapp')], 'syl',
            '( %s -> %s = <. ( %s ++ %s ) , ( %s + %s ) >. )' % (pj, PG('( %s ++ %s )' % (P0_, S1)), P1(P0_), P1(S1), P2(P0_), P2(S1)))
    e1 = s([s([pf], 'fveq2d', '( %s -> %s = %s )' % (pj, PG(P1_), PG('( %s ++ %s )' % (P0_, S1)))), app], 'eqtrd',
           '( %s -> %s = <. ( %s ++ %s ) , ( %s + %s ) >. )' % (pj, PG(P1_), P1(P0_), P1(S1), P2(P0_), P2(S1)))
    cl0 = s([s([fzj, p0w], 'jca', '( %s -> ( %s /\\ %s e. Word NN0 ) )' % (pj, FZG, P0_)), w.inst('poolgocl')], 'syl', '( %s -> %s e. %s )' % (pj, PG(P0_), WN))
    cls = s([s([fzj, s1w], 'jca', '( %s -> ( %s /\\ %s e. Word NN0 ) )' % (pj, FZG, S1)), w.inst('poolgocl')], 'syl', '( %s -> %s e. %s )' % (pj, PG(S1), WN))
    a0, b0 = paircl(w, pj, PG(P0_), cl0, 'Word NN0', 'NN0')
    a1, b1 = paircl(w, pj, PG(S1), cls, 'Word NN0', 'NN0')
    X1 = '( %s ++ %s )' % (P1(P0_), P1(S1))
    X2 = '( %s + %s )' % (P2(P0_), P2(S1))
    x1v = s([s([a0, a1, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word NN0 )' % (pj, X1))], 'elexd', '( %s -> %s e. _V )' % (pj, X1))
    x2v = s([s([b0, b1], 'nn0addcld', '( %s -> %s e. NN0 )' % (pj, X2))], 'elexd', '( %s -> %s e. _V )' % (pj, X2))
    f2 = projeq(w, pj, PG(P1_), e1, X1, X2, x1v, x2v, 2)
    dif = s([s([f2], 'oveq1d', '( %s -> ( %s - %s ) = ( %s - %s ) )' % (pj, P2(P1_), P2(P0_), X2, P2(P0_))),
             s([s([b0], 'nn0cnd', '( %s -> %s e. CC )' % (pj, P2(P0_))), s([b1], 'nn0cnd', '( %s -> %s e. CC )' % (pj, P2(S1))), w.inst('pncan2')], 'syl2anc',
               '( %s -> ( %s - %s ) = %s )' % (pj, X2, P2(P0_), P2(S1)))], 'eqtrd', '( %s -> ( %s - %s ) = %s )' % (pj, P2(P1_), P2(P0_), P2(S1)))
    SUML = 'sum_ j e. ( 0 ..^ %s ) %s' % (NLW, P2(S1))
    SUMD = 'sum_ j e. ( 0 ..^ %s ) ( %s - %s )' % (NLW, P2(P1_), P2(P0_))
    se = s([s([dif], 'eqcomd', '( %s -> %s = ( %s - %s ) )' % (pj, P2(S1), P2(P1_), P2(P0_)))], 'sumeq2dv', '( %s -> %s = %s )' % (A, SUML, SUMD))
    KF = lambda k: P2('( L prefix %s )' % k)

    def kcong(a_):
        e = s([], 'id', '( k = %s -> k = %s )' % (a_, a_))
        cg, new = w.congr(KF('k'), {'k': a_}, 'k = %s' % a_, {'k': e})
        assert new == KF(a_), new
        return cg
    nw = s([lw, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (A, NLW))
    huz = s([nw, s([s([], 'nn0uz', 'NN0 = ( ZZ>= ` 0 )')], 'a1i', '( %s -> NN0 = ( ZZ>= ` 0 ) )' % A)], 'eleqtrd', '( %s -> %s e. ( ZZ>= ` 0 ) )' % (A, NLW))
    pk = '( %s /\\ k e. ( 0 ... %s ) )' % (A, NLW)
    fzk = s([s([], 'simpl', '( %s -> %s )' % (pk, A))], 'simpld', '( %s -> %s )' % (pk, FZG))
    lwk = s([s([], 'simpl', '( %s -> %s )' % (pk, A))], 'simprd', '( %s -> L e. Word NN0 )' % pk)
    pkw = s([lwk, w.inst('pfxcl')], 'syl', '( %s -> ( L prefix k ) e. Word NN0 )' % pk)
    clk = s([s([fzk, pkw], 'jca', '( %s -> ( %s /\\ ( L prefix k ) e. Word NN0 ) )' % (pk, FZG)), w.inst('poolgocl')], 'syl',
            '( %s -> %s e. %s )' % (pk, PG('( L prefix k )'), WN))
    kac = s([s([s([clk, w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (pk, KF('k')))], 'nn0cnd', '( %s -> %s e. CC )' % (pk, KF('k')))], 'id', '') if False else \
        s([s([clk, w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (pk, KF('k')))], 'nn0cnd', '( %s -> %s e. CC )' % (pk, KF('k')))
    tel = s([kcong('j'), kcong('( j + 1 )'), kcong('0'), kcong(NLW), huz, kac], 'telfsumo2',
            '( %s -> %s = ( %s - %s ) )' % (A, SUMD, KF(NLW), KF('0')))
    # ( L prefix ( # L ) ) = L , ( L prefix 0 ) = (/)
    e_n = s([s([s([lw, w.inst('pfxid')], 'syl', '( %s -> ( L prefix %s ) = L )' % (A, NLW))], 'fveq2d', '( %s -> %s = %s )' % (A, PG('( L prefix %s )' % NLW), PG('L')))],
            'fveq2d', '( %s -> %s = %s )' % (A, KF(NLW), P2('L')))
    p00 = s([s([], 'pfx00', '( L prefix 0 ) = (/)')], 'a1i', '( %s -> ( L prefix 0 ) = (/) )' % A)
    p0 = s([fzg, w.inst('poolgo0')], 'syl', '( %s -> %s = <. (/) , 0 >. )' % (A, PG('(/)')))
    z = s([s([], '0ex', '(/) e. _V')], 'a1i', '( %s -> (/) e. _V )' % A)
    z2 = s([s([], 'c0ex', '0 e. _V')], 'a1i', '( %s -> 0 e. _V )' % A)
    q2 = projeq(w, A, PG('(/)'), p0, '(/)', '0', z, z2, 2)
    e_0 = s([s([s([p00], 'fveq2d', '( %s -> %s = %s )' % (A, PG('( L prefix 0 )'), PG('(/)')))], 'fveq2d', '( %s -> %s = %s )' % (A, KF('0'), P2('(/)'))), q2],
            'eqtrd', '( %s -> %s = 0 )' % (A, KF('0')))
    cll = s([s([fzg, lw], 'jca', '( %s -> ( %s /\\ L e. Word NN0 ) )' % (A, FZG)), w.inst('poolgocl')], 'syl', '( %s -> %s e. %s )' % (A, PG('L'), WN))
    pl = s([s([cll, w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (A, P2('L')))], 'nn0cnd', '( %s -> %s e. CC )' % (A, P2('L')))
    r = s([s([e_n, e_0], 'oveq12d', '( %s -> ( %s - %s ) = ( %s - 0 ) )' % (A, KF(NLW), KF('0'), P2('L'))),
           s([pl, w.inst('subid1')], 'syl', '( %s -> ( %s - 0 ) = %s )' % (A, P2('L'), P2('L')))], 'eqtrd', '( %s -> ( %s - %s ) = %s )' % (A, KF(NLW), KF('0'), P2('L')))
    w.qed([s([se, tel], 'eqtrd', '( %s -> %s = ( %s - %s ) )' % (A, SUML, KF(NLW), KF('0'))), r], 'eqtrd', ST_S)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
