"""Sortie v4b block 8a: the sieve inequality for the progression.

progmain  ( PH -> ( # ` TT ) <_ ( ( ( X / SS ) + ( Y x. ( ( 1 + ( log ` Y ) ) ^ 2 ) ) ) + Z ) )
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm import W
from v4b_lib import (A, P, PH, V, WF, X, Y, T, DV, OM, MS, SS, SF, ERR, TT, CT, SH, mkst)
from cl import lift

DVP = DV(P)
OMR = OM('d', 'r')
RMD = '( %s - ( ( %s ` d ) x. %s ) )' % (MS('d'), V, X)
BODY = '( ( 3 ^ %s ) x. ( abs ` %s ) )' % (OMR, RMD)
IFE = 'if ( d <_ %s , %s , 0 )' % (Y, BODY)
IFG = 'if ( ( %s gcd n ) = 1 , ( %s ` n ) , 0 )' % (P, WF)
RHS = '( %s x. ( ( 1 + ( log ` %s ) ) ^ 2 ) )' % (Y, Y)
ELD = '( d e. %s <-> ( d e. NN /\\ d || %s ) )' % (DVP, P)
CTD = CT('d')
WV0 = lambda w, v: w.s([w.s([], 'eqidd', '( c = %s -> 1 = 1 )' % v),
                        w.s([], 'eqid', '%s = %s' % (WF, WF))], 'fvmptg',
                       '( ( %s e. NN /\\ 1 e. _V ) -> ( %s ` %s ) = 1 )' % (v, WF, v))


def afin_steps(w, st):
    fzf1 = st([], 'fzfid', '( 1 ... N ) e. Fin')
    return st([fzf1, st([w.s([], 'ssrab2', '%s C_ ( 1 ... N )' % A)], 'a1i',
                        '%s C_ ( 1 ... N )' % A)], 'ssfid', '%s e. Fin' % A)


def sf_real(w, st, afin):
    AA = '( %s /\\ n e. %s )' % (PH, A)
    sa = mkst(w, AA)
    anel = sa([], 'simpr', 'n e. %s' % A)
    anfz = sa([anel, w.inst('elrabi')], 'syl', 'n e. ( 1 ... N )')
    annn = sa([sa([w.s([], 'fz1ssnn', '( 1 ... N ) C_ NN')], 'a1i', '( 1 ... N ) C_ NN'),
               anfz], 'sseldd', 'n e. NN')
    awv = sa([annn, sa([w.s([], '1ex', '1 e. _V')], 'a1i', '1 e. _V'), WV0(w, 'n')], 'syl2anc',
             '( %s ` n ) = 1' % WF)
    are = sa([sa([awv, sa([], '1red', '1 e. RR')], 'eqeltrd', '( %s ` n ) e. RR' % WF),
              sa([], '0red', '0 e. RR')], 'ifcld', '%s e. RR' % IFG)
    return st([afin, are], 'fsumrecl', '%s e. RR' % SF)


def err_real(w, st, phs):
    pn = st([], 'progpnn',
            '( ( %s e. NN /\\ ( mmu ` %s ) =/= 0 ) /\\ { q e. Prime | q || %s } = %s )'
            % (P, P, P, T))
    pnn = st([st([pn], 'simpld', '( %s e. NN /\\ ( mmu ` %s ) =/= 0 )' % (P, P))], 'simpld',
             '%s e. NN' % P)
    dfin = st([pnn, w.inst('dvdsfi')], 'syl', '%s e. Fin' % DVP)
    eld = w.s([w.s([], 'breq1', '( x = d -> ( x || %s <-> d || %s ) )' % (P, P))], 'elrab', ELD)
    AD = '( %s /\\ d e. %s )' % (PH, DVP)
    sd = mkst(w, AD)
    LD = lambda s: lift(w, s, AD)
    dpair = sd([sd([], 'simpr', 'd e. %s' % DVP), sd([eld], 'a1i', ELD)], 'mpbid',
               '( d e. NN /\\ d || %s )' % P)
    dnn = sd([dpair], 'simpld', 'd e. NN')
    ddv = sd([dpair], 'simprd', 'd || %s' % P)
    omn = sd([sd([sd([dnn, w.inst('prmdvdsfi')], 'syl', '{ p e. Prime | p || d } e. Fin'),
                  sd([w.s([w.s([], 'breq1', '( p = r -> ( p || d <-> r || d ) )')], 'cbvrabv',
                          '{ p e. Prime | p || d } = { r e. Prime | r || d }')], 'a1i',
                     '{ p e. Prime | p || d } = { r e. Prime | r || d }')], 'eqeltrrd',
                 '{ r e. Prime | r || d } e. Fin'), w.inst('hashcl')], 'syl', '%s e. NN0' % OMR)
    powre = sd([sd([w.s([], '3re', '3 e. RR')], 'a1i', '3 e. RR'), omn], 'reexpcld',
               '( 3 ^ %s ) e. RR' % OMR)
    phd = LD(phs)
    ms = sd([sd([phd, dnn], 'jca', '( %s /\\ d e. NN )' % PH), w.inst('progmsum')], 'syl',
            '%s = ( # ` %s )' % (MS('d'), CTD))
    fzf = sd([], 'fzfid', '( 1 ... N ) e. Fin')
    ctfin = sd([fzf, sd([w.s([], 'ssrab2', '%s C_ ( 1 ... N )' % CTD)], 'a1i',
                        '%s C_ ( 1 ... N )' % CTD)], 'ssfid', '%s e. Fin' % CTD)
    msre = sd([ms, sd([sd([ctfin, w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % CTD)],
                      'nn0red', '( # ` %s ) e. RR' % CTD)], 'eqeltrd', '%s e. RR' % MS('d'))
    vcl = sd([phd, w.inst('progvcl')], 'syl', '%s : NN --> RR' % V)
    vdre = sd([vcl, dnn], 'ffvelcdmd', '( %s ` d ) e. RR' % V)
    nre = sd([sd([phd], 'simp3d', 'N e. NN0')], 'nn0red', 'N e. RR')
    mnn = sd([sd([phd], 'simp1d', 'M e. ( ZZ>= ` 2 )'), w.inst('eluz2nn')], 'syl', 'M e. NN')
    xre = sd([nre, sd([mnn], 'nnred', 'M e. RR'), sd([mnn], 'nnne0d', 'M =/= 0')],
             'redivcld', '%s e. RR' % X)
    rmre = sd([msre, sd([vdre, xre], 'remulcld', '( ( %s ` d ) x. %s ) e. RR' % (V, X))],
              'resubcld', '%s e. RR' % RMD)
    absre = sd([sd([rmre], 'recnd', '%s e. CC' % RMD)], 'abscld', '( abs ` %s ) e. RR' % RMD)
    ifere = sd([sd([powre, absre], 'remulcld', '%s e. RR' % BODY),
                sd([], '0red', '0 e. RR')], 'ifcld', '%s e. RR' % IFE)
    return st([dfin, ifere], 'fsumrecl', '%s e. RR' % ERR)


def progmain():
    w = W('progmain', 'The count of primes up to N in the progression, bounded through the '
                      'Selberg sieve by the main term, the error term and the sifting level.')
    st = mkst(w, PH)
    phs = st([], 'id', PH)
    znn = st([], 'simp2', 'Z e. NN')
    nn0 = st([], 'simp3', 'N e. NN0')
    zre = st([znn], 'nnred', 'Z e. RR')
    mnn = st([st([], 'simp1', 'M e. ( ZZ>= ` 2 )'), w.inst('eluz2nn')], 'syl', 'M e. NN')
    two = st([w.s([], '2nn0', '2 e. NN0')], 'a1i', '2 e. NN0')
    ynn = st([znn, two, w.inst('nnexpcl')], 'syl2anc', '%s e. NN' % Y)
    yre = st([ynn], 'nnred', '%s e. RR' % Y)
    yrp = st([ynn, w.inst('nnrp')], 'syl', '%s e. RR+' % Y)
    rhsre = st([yre, st([st([st([], '1red', '1 e. RR'),
                             st([yrp], 'relogcld', '( log ` %s ) e. RR' % Y)], 'readdcld',
                             '( 1 + ( log ` %s ) ) e. RR' % Y)], 'resqcld',
                        '( ( 1 + ( log ` %s ) ) ^ 2 ) e. RR' % Y)], 'remulcld',
               '%s e. RR' % RHS)
    xre = st([st([nn0], 'nn0red', 'N e. RR'), st([mnn], 'nnred', 'M e. RR'),
              st([mnn], 'nnne0d', 'M =/= 0')], 'redivcld', '%s e. RR' % X)
    sh = st([], 'progsh', SH)
    ssrp = st([sh, w.inst('ssrp')], 'syl', '%s e. RR+' % SS)
    xssre = st([xre, st([ssrp], 'rpred', '%s e. RR' % SS),
                st([ssrp], 'rpne0d', '%s =/= 0' % SS)], 'redivcld', '( %s / %s ) e. RR' % (X, SS))
    afin = afin_steps(w, st)
    sfre = sf_real(w, st, afin)
    errre = err_real(w, st, phs)
    ttfin = st([st([], 'fzfid', '( 0 ... N ) e. Fin'),
                st([w.s([], 'ssrab2', '%s C_ ( 0 ... N )' % TT)], 'a1i',
                   '%s C_ ( 0 ... N )' % TT)], 'ssfid', '%s e. Fin' % TT)
    httre = st([st([ttfin, w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % TT)], 'nn0red',
               '( # ` %s ) e. RR' % TT)
    cnt = st([], 'progcnt', '( # ` %s ) <_ ( %s + Z )' % (TT, SF))
    sel = st([], 'progsel', '%s <_ ( ( %s / %s ) + %s )' % (SF, X, SS, ERR))
    err = st([], 'progerr', '%s <_ %s' % (ERR, RHS))
    add1 = st([errre, rhsre, xssre, err], 'leadd2dd',
              '( ( %s / %s ) + %s ) <_ ( ( %s / %s ) + %s )' % (X, SS, ERR, X, SS, RHS))
    sum1 = st([xssre, errre], 'readdcld', '( ( %s / %s ) + %s ) e. RR' % (X, SS, ERR))
    sum2 = st([xssre, rhsre], 'readdcld', '( ( %s / %s ) + %s ) e. RR' % (X, SS, RHS))
    sfle = st([sfre, sum1, sum2, sel, add1], 'letrd',
              '%s <_ ( ( %s / %s ) + %s )' % (SF, X, SS, RHS))
    add2 = st([sfre, sum2, zre, sfle], 'leadd1dd',
              '( %s + Z ) <_ ( ( ( %s / %s ) + %s ) + Z )' % (SF, X, SS, RHS))
    w.qed([httre, st([sfre, zre], 'readdcld', '( %s + Z ) e. RR' % SF),
           st([sum2, zre], 'readdcld', '( ( ( %s / %s ) + %s ) + Z ) e. RR' % (X, SS, RHS)),
           cnt, add2], 'letrd',
          '( %s -> ( # ` %s ) <_ ( ( ( %s / %s ) + %s ) + Z ) )' % (PH, TT, X, SS, RHS))
    return w


def main(names=None):
    fns = {'progmain': progmain}
    ok = True
    for nm in (names or ['progmain']):
        ok = fns[nm]().run() and ok
    return ok


if __name__ == '__main__':
    sys.exit(0 if main(sys.argv[1:] or None) else 1)
