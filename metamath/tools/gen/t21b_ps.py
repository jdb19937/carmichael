"""Sortie T21b: t21psd (psiChar_one_sub_le)."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from t21b_base import *

RNG = '( 1 ... ( |_ ` Y ) )'
LN = '( ZRHom ` ( Z/nZ ` N ) )'
L1 = '( ZRHom ` ( Z/nZ ` 1 ) )'
SS = '{ k e. %s | ( k gcd N ) =/= 1 }' % RNG
DBN = '( Base ` ( DChr ` N ) )'
AN = '( ( %s ` ( %s ` n ) ) x. ( Lam ` n ) )' % (U0, LN)
BN = '( ( %s ` ( %s ` n ) ) x. ( Lam ` n ) )' % (U01, L1)
DN_ = '( %s - %s )' % (AN, BN)


def u0base(w, ante, n='N'):
    g = w.s([], 'eqid', '( DChr ` %s ) = ( DChr ` %s )' % (n, n))
    ab = w.s([g], 'dchrabl', '( %s e. NN -> ( DChr ` %s ) e. Abel )' % (n, n))
    b = w.s([], 'eqid', '( Base ` ( DChr ` %s ) ) = ( Base ` ( DChr ` %s ) )' % (n, n))
    o = w.s([], 'eqid', '( 0g ` ( DChr ` %s ) ) = ( 0g ` ( DChr ` %s ) )' % (n, n))
    gi = w.s([b, o], 'grpidcl', '( ( DChr ` %s ) e. Grp -> ( 0g ` ( DChr ` %s ) ) e. ( Base ` ( DChr ` %s ) ) )' % (n, n, n))
    return ab, gi


def gen_psd():
    w = W('t21psd', 'The principal character mod ` N ` against the character mod ` 1 ` : the twisted ` psi ` differ by the prime powers sharing a factor with ` N ` , at most ` omega ( N ) log Y ` (Lean ` psiChar_one_sub_le ` ; ~ psicharval , ~ dchr1 , ~ dchrn0 , ~ vmancoprm ).')
    A0, concl = split_imp(SB['t21psd'])
    s = S_(w, A0)
    nn = s([], 'simpl', 'N e. NN'); yr = s([], 'simprl', 'Y e. RR'); y1 = s([], 'simprr', '1 <_ Y')
    ab, gi = u0base(w, A0)
    grp = s([s([nn, ab], 'syl', '( DChr ` N ) e. Abel'), w.inst('ablgrp')], 'syl', '( DChr ` N ) e. Grp')
    u0b = s([grp, gi], 'syl', '%s e. %s' % (U0, DBN))
    ab1, gi1 = u0base(w, A0, '1')
    u1b = w.s([w.s([w.s([w.s([], '1nn', '1 e. NN'), ab1], 'ax-mp', '( DChr ` 1 ) e. Abel'), w.inst('ablgrp')], 'ax-mp', '( DChr ` 1 ) e. Grp'), gi1], 'ax-mp', '%s e. ( Base ` ( DChr ` 1 ) )' % U01)
    u1b = s([u1b], 'a1i', '%s e. ( Base ` ( DChr ` 1 ) )' % U01)
    one = s([w.s([], '1nn', '1 e. NN')], 'a1i', '1 e. NN')
    pv = s([s([nn, u0b, yr], '3jca', '( N e. NN /\\ %s e. %s /\\ Y e. RR )' % (U0, DBN)), w.inst('psicharval')], 'syl', '( %s ( psiChar ` N ) Y ) = sum_ n e. %s %s' % (U0, RNG, AN))
    pv1 = s([s([one, u1b, yr], '3jca', '( 1 e. NN /\\ %s e. ( Base ` ( DChr ` 1 ) ) /\\ Y e. RR )' % U01), w.inst('psicharval')], 'syl', '( %s ( psiChar ` 1 ) Y ) = sum_ n e. %s %s' % (U01, RNG, BN))
    rf = s([], 'fzfid', '%s e. Fin' % RNG)
    An = '( %s /\\ n e. %s )' % (A0, RNG)
    sn = S_(w, An)
    nin = sn([sn([], 'simpr', 'n e. %s' % RNG), w.inst('elfznn')], 'syl', 'n e. NN')
    nz = sn([nin], 'nnzd', 'n e. ZZ')
    lam = sn([nin, w.inst('vmacl')], 'syl', '( Lam ` n ) e. RR')
    lamc = sn([lam], 'recnd', '( Lam ` n ) e. CC')
    lam0 = sn([nin, w.inst('vmage0')], 'syl', '0 <_ ( Lam ` n )')
    chv = sn([sn([lift(w, nn, An), lift(w, u0b, An), nz], 'jca', 'x')], 'x', 'x') if False else None
    chv = ap(w, An, [lift(w, nn, An), lift(w, u0b, An), nz], 'cen2chv', '( ( %s ` ( %s ` n ) ) e. CC /\\ ( abs ` ( %s ` ( %s ` n ) ) ) <_ 1 )' % (U0, LN, U0, LN))
    ac = sn([sn([chv], 'simpld', '( %s ` ( %s ` n ) ) e. CC' % (U0, LN)), lamc], 'mulcld', '%s e. CC' % AN)
    x1v = ap(w, An, [lift(w, u1b, An), nz], 'zc1x1', '( %s ` ( %s ` n ) ) = 1' % (U01, L1))
    bv = sn([sn([x1v], 'oveq1d', '%s = ( 1 x. ( Lam ` n ) )' % BN), sn([lamc], 'mullidd', '( 1 x. ( Lam ` n ) ) = ( Lam ` n )')], 'eqtrd', '%s = ( Lam ` n )' % BN)
    bc = sn([bv, lamc], 'eqeltrd', '%s e. CC' % BN)
    dc = sn([ac, bc], 'subcld', '%s e. CC' % DN_)
    fs = s([rf, ac, bc], 'fsumsub', 'sum_ n e. %s %s = ( sum_ n e. %s %s - sum_ n e. %s %s )' % (RNG, DN_, RNG, AN, RNG, BN))
    deq = s([s([pv, pv1], 'oveq12d', '( ( %s ( psiChar ` N ) Y ) - ( %s ( psiChar ` 1 ) Y ) ) = ( sum_ n e. %s %s - sum_ n e. %s %s )' % (U0, U01, RNG, AN, RNG, BN)), s([fs], 'eqcomd', '( sum_ n e. %s %s - sum_ n e. %s %s ) = sum_ n e. %s %s' % (RNG, AN, RNG, BN, RNG, DN_))],
            'eqtrd', '( ( %s ( psiChar ` N ) Y ) - ( %s ( psiChar ` 1 ) Y ) ) = sum_ n e. %s %s' % (U0, U01, RNG, DN_))
    fa = s([rf, dc], 'fsumabs', '( abs ` sum_ n e. %s %s ) <_ sum_ n e. %s ( abs ` %s )' % (RNG, DN_, RNG, DN_))
    # ZRHom n e. Base, Unit facts
    ZN = '( Z/nZ ` N )'
    eY = w.s([], 'eqid', '%s = %s' % (ZN, ZN)); eB = w.s([], 'eqid', '( Base ` %s ) = ( Base ` %s )' % (ZN, ZN)); eL = w.s([], 'eqid', '%s = %s' % (LN, LN))
    eU = w.s([], 'eqid', '( Unit ` %s ) = ( Unit ` %s )' % (ZN, ZN))
    eG = w.s([], 'eqid', '( DChr ` N ) = ( DChr ` N )'); eD = w.s([], 'eqid', '%s = %s' % (DBN, DBN)); eO = w.s([], 'eqid', '%s = %s' % (U0, U0))
    fo = w.s([eY, eB, eL], 'znzrhfo', '( N e. NN0 -> %s : ZZ -onto-> ( Base ` %s ) )' % (LN, ZN))
    ff = sn([sn([sn([lift(w, nn, An)], 'nnnn0d', 'N e. NN0'), fo], 'syl', '%s : ZZ -onto-> ( Base ` %s )' % (LN, ZN)), w.inst('fof')], 'syl', '%s : ZZ --> ( Base ` %s )' % (LN, ZN))
    lb = sn([ff, nz], 'ffvelcdmd', '( %s ` n ) e. ( Base ` %s )' % (LN, ZN))
    un = w.s([eY, eU, eL], 'znunit', '( ( N e. NN0 /\\ n e. ZZ ) -> ( ( %s ` n ) e. ( Unit ` %s ) <-> ( n gcd N ) = 1 ) )' % (LN, ZN))
    unn = sn([sn([sn([lift(w, nn, An)], 'nnnn0d', 'N e. NN0'), nz], 'jca', '( N e. NN0 /\\ n e. ZZ )'), un], 'syl', '( ( %s ` n ) e. ( Unit ` %s ) <-> ( n gcd N ) = 1 )' % (LN, ZN))
    n0 = w.s([eG, eY, eD, eB, eU, lift(w, u0b, An), lb], 'dchrn0', '( %s -> ( ( %s ` ( %s ` n ) ) =/= 0 <-> ( %s ` n ) e. ( Unit ` %s ) ) )' % (An, U0, LN, LN, ZN))
    # membership in SS
    ce = w.s([w.s([], 'oveq1', '( k = n -> ( k gcd N ) = ( n gcd N ) )')], 'neeq1d', '( k = n -> ( ( k gcd N ) =/= 1 <-> ( n gcd N ) =/= 1 ) )')
    els = w.s([ce], 'elrab', '( n e. %s <-> ( n e. %s /\\ ( n gcd N ) =/= 1 ) )' % (SS, RNG))
    # on SS: abs ( a - b ) = Lam n
    As = '( %s /\\ n e. %s )' % (A0, SS)
    ss_ = S_(w, As)
    sm = ss_([ss_([], 'simpr', 'n e. %s' % SS), els], 'sylib', '( n e. %s /\\ ( n gcd N ) =/= 1 )' % RNG)
    toAn = ss_([ss_([], 'simpl', A0), ss_([sm], 'simpld', 'n e. %s' % RNG)], 'jca', An)
    via = lambda st, f: ss_([toAn, w.s([st], 'x', 'x') if False else st], 'syl', f) if False else None
    V = lambda st, f: w.s([toAn, st], 'syl', '( %s -> %s )' % (As, f)) if False else None

    def viaA(st, f):
        # st : ( An -> f )  ==>  ( As -> f )
        imp = w.s([st], 'ex', 'x') if False else None
        return ss_([toAn, w.s([st], 'x', 'x')], 'x', 'x') if False else None
    # use lemma instances in closed form: turn ( An -> f ) into ( As -> f ) through a syl on toAn
    def to_s(st, f):
        return ss_([toAn, st], 'syl', f)
    gne = ss_([sm], 'simprd', '( n gcd N ) =/= 1')
    nun = ss_([ss_([gne], 'neneqd', '-. ( n gcd N ) = 1'), to_s(w.s([unn], 'notbid', '( %s -> ( -. ( %s ` n ) e. ( Unit ` %s ) <-> -. ( n gcd N ) = 1 ) )' % (An, LN, ZN)),
                                                                   '( -. ( %s ` n ) e. ( Unit ` %s ) <-> -. ( n gcd N ) = 1 )' % (LN, ZN))], 'mpbird', '-. ( %s ` n ) e. ( Unit ` %s )' % (LN, ZN))
    v0n = ss_([nun, to_s(w.s([n0], 'necon1bbid', '( %s -> ( -. ( %s ` n ) e. ( Unit ` %s ) <-> ( %s ` ( %s ` n ) ) = 0 ) )' % (An, LN, ZN, U0, LN)),
                                                         '( -. ( %s ` n ) e. ( Unit ` %s ) <-> ( %s ` ( %s ` n ) ) = 0 )' % (LN, ZN, U0, LN))], 'mpbid', '( %s ` ( %s ` n ) ) = 0' % (U0, LN))
    lamcs = to_s(lamc, '( Lam ` n ) e. CC')
    a0 = ss_([ss_([v0n], 'oveq1d', '%s = ( 0 x. ( Lam ` n ) )' % AN), ss_([lamcs], 'mul02d', '( 0 x. ( Lam ` n ) ) = 0')], 'eqtrd', '%s = 0' % AN)
    ds = ss_([a0, to_s(bv, '%s = ( Lam ` n )' % BN)], 'oveq12d', '%s = ( 0 - ( Lam ` n ) )' % DN_)
    ds2 = ss_([ds, ss_([lamcs], 'df-neg', 'x') if False else ss_([ss_([], '0cnd', '0 e. CC') if False else None], 'x', 'x') if False else None], 'x', 'x') if False else None
    ng = ss_([ds, ss_([w.s([], 'df-neg', '-u ( Lam ` n ) = ( 0 - ( Lam ` n ) )')], 'a1i', '-u ( Lam ` n ) = ( 0 - ( Lam ` n ) )')], 'eqtr4d', '%s = -u ( Lam ` n )' % DN_)
    abn = ss_([ss_([ng], 'fveq2d', '( abs ` %s ) = ( abs ` -u ( Lam ` n ) )' % DN_), ss_([lamcs], 'absnegd', '( abs ` -u ( Lam ` n ) ) = ( abs ` ( Lam ` n ) )')], 'eqtrd', '( abs ` %s ) = ( abs ` ( Lam ` n ) )' % DN_)
    abl = ss_([abn, ss_([to_s(lam, '( Lam ` n ) e. RR'), to_s(lam0, '0 <_ ( Lam ` n )')], 'absidd', '( abs ` ( Lam ` n ) ) = ( Lam ` n )')], 'eqtrd', '( abs ` %s ) = ( Lam ` n )' % DN_)
    # off SS: a - b = 0
    Ao = '( %s /\\ n e. ( %s \\ %s ) )' % (A0, RNG, SS)
    so = S_(w, Ao)
    nr = so([so([], 'simpr', 'n e. ( %s \\ %s )' % (RNG, SS)), w.inst('eldifi')], 'syl', 'n e. %s' % RNG)
    nns = so([so([], 'simpr', 'n e. ( %s \\ %s )' % (RNG, SS)), w.inst('eldifn')], 'syl', '-. n e. %s' % SS)
    toAo = so([so([], 'simpl', A0), nr], 'jca', An)
    to_o = lambda st, f: so([toAo, st], 'syl', f)
    Ag = '( %s /\\ ( n gcd N ) =/= 1 )' % Ao
    gin = w.s([w.s([lift(w, nr, Ag), w.s([], 'simpr', '( %s -> ( n gcd N ) =/= 1 )' % Ag)], 'jca', '( %s -> ( n e. %s /\\ ( n gcd N ) =/= 1 ) )' % (Ag, RNG)), els], 'sylibr', '( %s -> n e. %s )' % (Ag, SS))
    g1 = so([so([gin, lift(w, nns, Ag)], 'pm2.65da', '-. ( n gcd N ) =/= 1'), w.s([], 'nne', '( -. ( n gcd N ) =/= 1 <-> ( n gcd N ) = 1 )')], 'sylib', '( n gcd N ) = 1')
    uu = so([g1, to_o(unn, '( ( %s ` n ) e. ( Unit ` %s ) <-> ( n gcd N ) = 1 )' % (LN, ZN))], 'mpbird', '( %s ` n ) e. ( Unit ` %s )' % (LN, ZN))
    v1 = w.s([eG, eY, eO, eU, lift(w, nn, Ao), uu], 'dchr1', '( %s -> ( %s ` ( %s ` n ) ) = 1 )' % (Ao, U0, LN))
    lamco = to_o(lamc, '( Lam ` n ) e. CC')
    av = so([so([v1], 'oveq1d', '%s = ( 1 x. ( Lam ` n ) )' % AN), so([lamco], 'mullidd', '( 1 x. ( Lam ` n ) ) = ( Lam ` n )')], 'eqtrd', '%s = ( Lam ` n )' % AN)
    d0 = so([so([av, to_o(bv, '%s = ( Lam ` n )' % BN)], 'oveq12d', '%s = ( ( Lam ` n ) - ( Lam ` n ) )' % DN_), so([lamco], 'subidd', '( ( Lam ` n ) - ( Lam ` n ) ) = 0')], 'eqtrd', '%s = 0' % DN_)
    ad0 = so([so([d0], 'fveq2d', '( abs ` %s ) = ( abs ` 0 )' % DN_), so([w.s([], 'abs0', '( abs ` 0 ) = 0')], 'a1i', '( abs ` 0 ) = 0')], 'eqtrd', '( abs ` %s ) = 0' % DN_)
    ssr = s([w.s([], 'ssrab2', '%s C_ %s' % (SS, RNG))], 'a1i', '%s C_ %s' % (SS, RNG))
    adcs = ss_([toAn, w.s([dc], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (An, DN_))], 'syl', '( abs ` %s ) e. RR' % DN_)
    adcs = ss_([adcs], 'recnd', '( abs ` %s ) e. CC' % DN_)
    fss = s([ssr, adcs, ad0, rf], 'fsumss', 'sum_ n e. %s ( abs ` %s ) = sum_ n e. %s ( abs ` %s )' % (SS, DN_, RNG, DN_))
    sl = s([abl], 'sumeq2dv', 'sum_ n e. %s ( abs ` %s ) = sum_ n e. %s ( Lam ` n )' % (SS, DN_, SS))
    vm = s([s([nn, yr, y1], '3jca', '( N e. NN /\\ Y e. RR /\\ 1 <_ Y )'), w.inst('vmancoprm')], 'syl', 'sum_ n e. %s ( Lam ` n ) <_ ( %s x. ( log ` Y ) )' % (SS, OM('N')))
    chain = s([s([fss], 'eqcomd', 'sum_ n e. %s ( abs ` %s ) = sum_ n e. %s ( abs ` %s )' % (RNG, DN_, SS, DN_)), sl], 'eqtrd', 'sum_ n e. %s ( abs ` %s ) = sum_ n e. %s ( Lam ` n )' % (RNG, DN_, SS))
    b1 = s([fa, chain], 'breqtrd', '( abs ` sum_ n e. %s %s ) <_ sum_ n e. %s ( Lam ` n )' % (RNG, DN_, SS))
    ssfin = s([rf, ssr], 'ssfid', '%s e. Fin' % SS)
    Asl = As
    lams = ss_([toAn, lam], 'syl', '( Lam ` n ) e. RR')
    slr = s([ssfin, lams], 'fsumrecl', 'sum_ n e. %s ( Lam ` n ) e. RR' % SS)
    sumr = s([rf, dc], 'fsumcl', 'sum_ n e. %s %s e. CC' % (RNG, DN_))
    absr = s([sumr], 'abscld', '( abs ` sum_ n e. %s %s ) e. RR' % (RNG, DN_))
    omr = s([s([s([s([nn, w.inst('prmdvdsfi')], 'syl', '{ p e. Prime | p || N } e. Fin'), w.inst('hashcl')], 'syl', '%s e. NN0' % OM('N'))], 'nn0red', '%s e. RR' % OM('N')),
             s([s([yr, lin.linarith(w, A0, [y1], '0 < Y', leaves={'Y': yr})], 'elrpd', 'Y e. RR+')], 'relogcld', '( log ` Y ) e. RR')], 'remulcld', '( %s x. ( log ` Y ) ) e. RR' % OM('N'))
    b2 = s([absr, slr, omr, b1, vm], 'letrd', '( abs ` sum_ n e. %s %s ) <_ ( %s x. ( log ` Y ) )' % (RNG, DN_, OM('N')))
    fin = s([s([deq], 'fveq2d', '( abs ` ( ( %s ( psiChar ` N ) Y ) - ( %s ( psiChar ` 1 ) Y ) ) ) = ( abs ` sum_ n e. %s %s )' % (U0, U01, RNG, DN_)), b2], 'eqbrtrd', concl)
    w.lines.append('qed:%s:idi |- %s' % (fin, SB['t21psd']))
    return go(w)


if __name__ == '__main__':
    gen_psd()
