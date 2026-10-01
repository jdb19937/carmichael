"""Sortie v4b block 6: the error sum of the progression sieve.

progerr  ( PH -> ERR <_ ( Y x. ( ( 1 + ( log ` Y ) ) ^ 2 ) ) )
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm import W
from v4b_lib import P, PH, V, X, Y, T, DV, OM, MS, ERR, CT, mkst
from cl import lift

DVP = DV(P)
OMR = OM('d', 'r')
OMQ = OM('d', 'q')
RMD = '( %s - ( ( %s ` d ) x. %s ) )' % (MS('d'), V, X)
BODY = '( ( 3 ^ %s ) x. ( abs ` %s ) )' % (OMR, RMD)
IFE = 'if ( d <_ %s , %s , 0 )' % (Y, BODY)
IFP = 'if ( d <_ %s , ( 3 ^ %s ) , 0 )' % (Y, OMR)
SOM = 'sum_ d e. %s %s' % (DVP, IFP)
SUB = '{ x e. NN | ( x || %s /\\ x <_ %s ) }' % (P, Y)
S3 = 'sum_ d e. %s ( 3 ^ %s )' % (SUB, OMQ)
S3R = 'sum_ d e. %s ( 3 ^ %s )' % (SUB, OMR)
RHS = '( %s x. ( ( 1 + ( log ` %s ) ) ^ 2 ) )' % (Y, Y)
CTD = CT('d')
ELD = '( d e. %s <-> ( d e. NN /\\ d || %s ) )' % (DVP, P)
ELS = '( d e. %s <-> ( d e. NN /\\ ( d || %s /\\ d <_ %s ) ) )' % (SUB, P, Y)


def progerr():
    w = W('progerr', 'The error sum of the progression sieve is at most the level times '
                     'the square of one plus its logarithm.')
    st = mkst(w, PH)
    muz = st([], 'simp1', 'M e. ( ZZ>= ` 2 )')
    znn = st([], 'simp2', 'Z e. NN')
    two = st([w.s([], '2nn0', '2 e. NN0')], 'a1i', '2 e. NN0')
    ynn = st([znn, two, w.inst('nnexpcl')], 'syl2anc', '%s e. NN' % Y)
    yre = st([ynn], 'nnred', '%s e. RR' % Y)
    pn = st([], 'progpnn',
            '( ( %s e. NN /\\ ( mmu ` %s ) =/= 0 ) /\\ { q e. Prime | q || %s } = %s )'
            % (P, P, P, T))
    pp = st([pn], 'simpld', '( %s e. NN /\\ ( mmu ` %s ) =/= 0 )' % (P, P))
    pnn = st([pp], 'simpld', '%s e. NN' % P)
    psq = st([pp], 'simprd', '( mmu ` %s ) =/= 0' % P)
    dfin = st([pnn, w.inst('dvdsfi')], 'syl', '%s e. Fin' % DVP)
    eld = w.s([w.s([], 'breq1', '( x = d -> ( x || %s <-> d || %s ) )' % (P, P))], 'elrab', ELD)
    els = w.s([w.s([w.s([], 'breq1', '( x = d -> ( x || %s <-> d || %s ) )' % (P, P)),
                    w.s([], 'breq1', '( x = d -> ( x <_ %s <-> d <_ %s ) )' % (Y, Y))],
                   'anbi12d',
                   '( x = d -> ( ( x || %s /\\ x <_ %s ) <-> ( d || %s /\\ d <_ %s ) ) )'
                   % (P, Y, P, Y))], 'elrab', ELS)
    # ---- step 1: fsumle ------------------------------------------------
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
    three = sd([w.s([], '3re', '3 e. RR')], 'a1i', '3 e. RR')
    th0 = sd([sd([], '0red', '0 e. RR'), three,
              sd([w.s([], '3pos', '0 < 3')], 'a1i', '0 < 3')], 'ltled', '0 <_ 3')
    powre = sd([three, omn], 'reexpcld', '( 3 ^ %s ) e. RR' % OMR)
    pow0 = sd([three, omn, th0, w.inst('expge0')], 'syl3anc', '0 <_ ( 3 ^ %s )' % OMR)
    phd = LD(st([], 'id', PH))
    rem = sd([sd([phd, sd([dnn, ddv], 'jca', '( d e. NN /\\ d || %s )' % P)],
                 'jca', '( %s /\\ ( d e. NN /\\ d || %s ) )' % (PH, P)), w.inst('progrem')],
             'syl', '( abs ` %s ) <_ 1' % RMD)
    ms = sd([sd([phd, dnn], 'jca', '( %s /\\ d e. NN )' % PH), w.inst('progmsum')], 'syl',
            '%s = ( # ` %s )' % (MS('d'), CTD))
    fzf = sd([], 'fzfid', '( 1 ... N ) e. Fin')
    ctss = sd([w.s([], 'ssrab2', '%s C_ ( 1 ... N )' % CTD)], 'a1i',
              '%s C_ ( 1 ... N )' % CTD)
    ctfin = sd([fzf, ctss], 'ssfid', '%s e. Fin' % CTD)
    msre = sd([ms, sd([sd([ctfin, w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % CTD)],
                      'nn0red', '( # ` %s ) e. RR' % CTD)], 'eqeltrd', '%s e. RR' % MS('d'))
    vcl = sd([phd, w.inst('progvcl')], 'syl', '%s : NN --> RR' % V)
    vdre = sd([vcl, dnn], 'ffvelcdmd', '( %s ` d ) e. RR' % V)
    nn0s = sd([sd([phd], 'simp3d', 'N e. NN0')], 'nn0red', 'N e. RR')
    mnn = sd([sd([phd], 'simp1d', 'M e. ( ZZ>= ` 2 )'), w.inst('eluz2nn')], 'syl', 'M e. NN')
    xre = sd([nn0s, sd([mnn], 'nnred', 'M e. RR'), sd([mnn], 'nnne0d', 'M =/= 0')],
             'redivcld', '%s e. RR' % X)
    rmre = sd([msre, sd([vdre, xre], 'remulcld', '( ( %s ` d ) x. %s ) e. RR' % (V, X))],
              'resubcld', '%s e. RR' % RMD)
    absre = sd([sd([rmre], 'recnd', '%s e. CC' % RMD)], 'abscld', '( abs ` %s ) e. RR' % RMD)
    bodyre = sd([powre, absre], 'remulcld', '%s e. RR' % BODY)
    ifere = sd([bodyre, sd([], '0red', '0 e. RR')], 'ifcld', '%s e. RR' % IFE)
    ifpre = sd([powre, sd([], '0red', '0 e. RR')], 'ifcld', '%s e. RR' % IFP)
    # the branchwise comparison
    AT = '( %s /\\ d <_ %s )' % (AD, Y)
    sT = mkst(w, AT)
    LT = lambda st_: lift(w, st_, AT)
    tcond = sT([], 'simpr', 'd <_ %s' % Y)
    t1 = sT([tcond], 'iftrued', '%s = %s' % (IFE, BODY))
    t2 = sT([tcond], 'iftrued', '%s = ( 3 ^ %s )' % (IFP, OMR))
    tmul = sT([LT(absre), sT([], '1red', '1 e. RR'), LT(powre), LT(pow0), LT(rem)],
              'lemul2ad', '( ( 3 ^ %s ) x. ( abs ` %s ) ) <_ ( ( 3 ^ %s ) x. 1 )'
              % (OMR, RMD, OMR))
    tmr = sT([sT([LT(powre)], 'recnd', '( 3 ^ %s ) e. CC' % OMR)], 'mulridd',
             '( ( 3 ^ %s ) x. 1 ) = ( 3 ^ %s )' % (OMR, OMR))
    tle = sT([tmul, tmr], 'breqtrd', '%s <_ ( 3 ^ %s )' % (BODY, OMR))
    tfin = sT([t1, sT([tle, t2], 'breqtrrd', '%s <_ %s' % (BODY, IFP))], 'eqbrtrd',
              '%s <_ %s' % (IFE, IFP))
    AFF = '( %s /\\ -. d <_ %s )' % (AD, Y)
    sF = mkst(w, AFF)
    fcond = sF([], 'simpr', '-. d <_ %s' % Y)
    f1 = sF([fcond], 'iffalsed', '%s = 0' % IFE)
    f2 = sF([fcond], 'iffalsed', '%s = 0' % IFP)
    ffin = sF([f1, sF([sF([w.s([], '0le0', '0 <_ 0')], 'a1i', '0 <_ 0'), f2], 'breqtrrd',
                      '0 <_ %s' % IFP)], 'eqbrtrd', '%s <_ %s' % (IFE, IFP))
    cmp = w.s([tfin, ffin], 'pm2.61dan', '( %s -> %s <_ %s )' % (AD, IFE, IFP))
    le1 = st([dfin, ifere, ifpre, cmp], 'fsumle', '%s <_ %s' % (ERR, SOM))
    # ---- step 2: down to the truncated divisor set ----------------------
    subss = st([w.s([w.s([w.s([], 'simpl',
                               '( ( x || %s /\\ x <_ %s ) -> x || %s )' % (P, Y, P))], 'a1i',
                         '( x e. NN -> ( ( x || %s /\\ x <_ %s ) -> x || %s ) )' % (P, Y, P))],
                    'ss2rabi', '%s C_ %s' % (SUB, DVP))], 'a1i', '%s C_ %s' % (SUB, DVP))
    AS = '( %s /\\ d e. %s )' % (PH, SUB)
    sS = mkst(w, AS)
    LS = lambda st_: lift(w, st_, AS)
    spair = sS([sS([], 'simpr', 'd e. %s' % SUB), sS([els], 'a1i', ELS)], 'mpbid',
               '( d e. NN /\\ ( d || %s /\\ d <_ %s ) )' % (P, Y))
    sle = sS([spair], 'simprrd', 'd <_ %s' % Y)
    sif = sS([sle], 'iftrued', '%s = ( 3 ^ %s )' % (IFP, OMR))
    ARR = '( %s /\\ d e. ( %s \\ %s ) )' % (PH, DVP, SUB)
    sR = mkst(w, ARR)
    rel = sR([], 'simpr', 'd e. ( %s \\ %s )' % (DVP, SUB))
    rin = sR([rel, w.inst('eldifi')], 'syl', 'd e. %s' % DVP)
    rnin = sR([rel, w.inst('eldifn')], 'syl', '-. d e. %s' % SUB)
    rpair = sR([rin, sR([eld], 'a1i', ELD)], 'mpbid', '( d e. NN /\\ d || %s )' % P)
    rnn = sR([rpair], 'simpld', 'd e. NN')
    rdv = sR([rpair], 'simprd', 'd || %s' % P)
    ALE = '( %s /\\ d <_ %s )' % (ARR, Y)
    sL = mkst(w, ALE)
    lcond = sL([], 'simpr', 'd <_ %s' % Y)
    lin = sL([lift(w, rnn, ALE),
              sL([lift(w, rdv, ALE), lcond], 'jca',
                 '( d || %s /\\ d <_ %s )' % (P, Y))], 'jca',
             '( d e. NN /\\ ( d || %s /\\ d <_ %s ) )' % (P, Y))
    lsub = sL([sL([els], 'a1i', ELS), lin], 'mpbird', 'd e. %s' % SUB)
    limp = sR([lsub], 'ex', '( d <_ %s -> d e. %s )' % (Y, SUB))
    rnle = sR([rnin, limp], 'mtod', '-. d <_ %s' % Y)
    rz = sR([rnle], 'iffalsed', '%s = 0' % IFP)
    snn = sS([spair], 'simpld', 'd e. NN')
    somn = sS([sS([sS([snn, w.inst('prmdvdsfi')], 'syl', '{ p e. Prime | p || d } e. Fin'),
                   sS([w.s([w.s([], 'breq1', '( p = r -> ( p || d <-> r || d ) )')], 'cbvrabv',
                           '{ p e. Prime | p || d } = { r e. Prime | r || d }')], 'a1i',
                      '{ p e. Prime | p || d } = { r e. Prime | r || d }')], 'eqeltrrd',
                  '{ r e. Prime | r || d } e. Fin'), w.inst('hashcl')], 'syl',
               '%s e. NN0' % OMR)
    spow = sS([sS([w.s([], '3re', '3 e. RR')], 'a1i', '3 e. RR'), somn], 'reexpcld',
              '( 3 ^ %s ) e. RR' % OMR)
    sifc = sS([sS([spow, sS([], '0red', '0 e. RR')], 'ifcld', '%s e. RR' % IFP)], 'recnd',
              '%s e. CC' % IFP)
    ss = st([subss, sifc, rz, dfin], 'fsumss',
            'sum_ d e. %s %s = %s' % (SUB, IFP, SOM))
    s3r = st([st([sif], 'sumeq2dv', 'sum_ d e. %s %s = %s' % (SUB, IFP, S3R)),
              ss], 'eqtr3d', '%s = %s' % (SOM, S3R))
    # ---- step 3: the change of bound variable in the exponent -----------
    cbq = sS([sS([w.s([w.s([], 'breq1', '( r = q -> ( r || d <-> q || d ) )')], 'cbvrabv',
                      '{ r e. Prime | r || d } = { q e. Prime | q || d }')], 'a1i',
                 '{ r e. Prime | r || d } = { q e. Prime | q || d }')], 'fveq2d',
              '%s = %s' % (OMR, OMQ))
    s3e = st([sS([cbq], 'oveq2d', '( 3 ^ %s ) = ( 3 ^ %s )' % (OMR, OMQ))], 'sumeq2dv',
             '%s = %s' % (S3R, S3))
    # ---- step 4: sum3omle ----------------------------------------------
    som = st([pnn, psq, ynn, w.inst('sum3omle')], 'syl3anc', '%s <_ %s' % (S3, RHS))
    fin = st([st([s3r, s3e], 'eqtrd', '%s = %s' % (SOM, S3)), som], 'eqbrtrd',
             '%s <_ %s' % (SOM, RHS))
    errre = st([dfin, ifere], 'fsumrecl', '%s e. RR' % ERR)
    somre = st([dfin, ifpre], 'fsumrecl', '%s e. RR' % SOM)
    yrp = st([ynn, w.inst('nnrp')], 'syl', '%s e. RR+' % Y)
    logy = st([yrp], 'relogcld', '( log ` %s ) e. RR' % Y)
    onep = st([st([], '1red', '1 e. RR'), logy], 'readdcld',
              '( 1 + ( log ` %s ) ) e. RR' % Y)
    sqre = st([onep], 'resqcld', '( ( 1 + ( log ` %s ) ) ^ 2 ) e. RR' % Y)
    rhsre = st([yre, sqre], 'remulcld', '%s e. RR' % RHS)
    w.qed([errre, somre, rhsre, le1, fin], 'letrd',
          '( %s -> %s <_ %s )' % (PH, ERR, RHS))
    return w


def main(names=None):
    fns = {'progerr': progerr}
    ok = True
    for nm in (names or ['progerr']):
        ok = fns[nm]().run() and ok
    return ok


if __name__ == '__main__':
    sys.exit(0 if main(sys.argv[1:] or None) else 1)
