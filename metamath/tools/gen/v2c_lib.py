"""Sortie v2c: shared expressions for the rest of the Selberg sieve."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from v2b_lib import *

BODY = '( 1 / ( 1 - ( V ` q ) ) )'


def RECP(v):
    """the factor of GT at a prime v"""
    return '( 1 / ( 1 - ( V ` %s ) ) )' % v


def QUOT(v):
    """GT at a prime v"""
    return '( ( V ` %s ) / ( 1 - ( V ` %s ) ) )' % (v, v)


def IQUOT(v):
    """1 / GT at a prime v"""
    return '( ( 1 - ( V ` %s ) ) / ( V ` %s ) )' % (v, v)


def IGT(X, q='q'):
    """1 / GT ( X )"""
    return '( 1 / %s )' % GT(X, q)


def pdivp(w, A, AP, p, K, sh, kz, kdp, pz, vf):
    """Facts about a prime divisor `p` of `K` under `AP = ( A /\\ p e. PF( K ) )`,
    given steps under `A`: sh (SH), kz (K e. ZZ), kdp (K || P), pz (P e. ZZ),
    vf (V : NN --> RR).  Returns a dict of step names under AP."""
    from cl import lift
    PFK = PF(K)
    sp = mkst(w, AP)
    elp = w.s([w.s([], 'breq1', '( r = %s -> ( r || %s <-> %s || %s ) )' % (p, K, p, K))],
              'elrab', '( %s e. %s <-> ( %s e. Prime /\\ %s || %s ) )' % (p, PFK, p, p, K))
    pc = sp([sp([elp], 'a1i', '( %s e. %s <-> ( %s e. Prime /\\ %s || %s ) )' % (p, PFK, p, p, K)),
             sp([], 'simpr', '%s e. %s' % (p, PFK))], 'mpbid',
            '( %s e. Prime /\\ %s || %s )' % (p, p, K))
    pprm = sp([pc], 'simpld', '%s e. Prime' % p)
    pdK = sp([pc], 'simprd', '%s || %s' % (p, K))
    pnn = sp([pprm, w.inst('prmnn')], 'syl', '%s e. NN' % p)
    ppz = sp([pprm, w.inst('prmz')], 'syl', '%s e. ZZ' % p)
    pdP = sp([sp([sp([ppz, lift(w, kz, AP), lift(w, pz, AP)], '3jca',
                     '( %s e. ZZ /\\ %s e. ZZ /\\ P e. ZZ )' % (p, K)), w.inst('dvdstr')], 'syl',
                 '( ( %s || %s /\\ %s || P ) -> %s || P )' % (p, K, K, p)),
              sp([pdK, lift(w, kdp, AP)], 'jca', '( %s || %s /\\ %s || P )' % (p, K, K))],
             'mpd', '%s || P' % p)
    vrp = sp([lift(w, sh, AP), sp([pnn, pdP], 'jca', '( %s e. NN /\\ %s || P )' % (p, p)),
              w.inst('vdrp')], 'syl2anc', '( V ` %s ) e. RR+' % p)
    subrp = sp([lift(w, sh, AP), sp([pprm, pdP], 'jca', '( %s e. Prime /\\ %s || P )' % (p, p)),
                w.inst('vsubrp')], 'syl2anc', '( 1 - ( V ` %s ) ) e. RR+' % p)
    return {'st': sp, 'prm': pprm, 'nn': pnn, 'z': ppz, 'dK': pdK, 'dP': pdP,
            'vrp': vrp, 'subrp': subrp}


def dvdfacts(w, A, AD, d, D, sh, dz, ddp, pz):
    """Facts about `d e. DV( D )` under `AD = ( A /\\ d e. DV( D ) )`."""
    from cl import lift
    DVD = DV(D)
    sd = mkst(w, AD)
    eld = w.s([w.s([], 'breq1', '( x = %s -> ( x || %s <-> %s || %s ) )' % (d, D, d, D))],
              'elrab', '( %s e. %s <-> ( %s e. NN /\\ %s || %s ) )' % (d, DVD, d, d, D))
    dc = sd([sd([eld], 'a1i', '( %s e. %s <-> ( %s e. NN /\\ %s || %s ) )' % (d, DVD, d, d, D)),
             sd([], 'simpr', '%s e. %s' % (d, DVD))], 'mpbid',
            '( %s e. NN /\\ %s || %s )' % (d, d, D))
    dnn = sd([dc], 'simpld', '%s e. NN' % d)
    ddD = sd([dc], 'simprd', '%s || %s' % (d, D))
    ddz = sd([dnn], 'nnzd', '%s e. ZZ' % d)
    ddP = sd([sd([sd([ddz, lift(w, dz, AD), lift(w, pz, AD)], '3jca',
                     '( %s e. ZZ /\\ %s e. ZZ /\\ P e. ZZ )' % (d, D)), w.inst('dvdstr')], 'syl',
                 '( ( %s || %s /\\ %s || P ) -> %s || P )' % (d, D, D, d)),
              sd([ddD, lift(w, ddp, AD)], 'jca', '( %s || %s /\\ %s || P )' % (d, D, D))],
             'mpd', '%s || P' % d)
    return {'st': sd, 'nn': dnn, 'z': ddz, 'dD': ddD, 'dP': ddP}


def dvpel(w, AV, v, pnn, y='x'):
    """Facts about `v e. DV( P )` under `AV = ( A /\\ v e. DV( P ) )`."""
    DVP = DV('P', y)
    sv = mkst(w, AV)
    elp = w.s([w.s([], 'breq1', '( %s = %s -> ( %s || P <-> %s || P ) )' % (y, v, y, v))], 'elrab',
              '( %s e. %s <-> ( %s e. NN /\\ %s || P ) )' % (v, DVP, v, v))
    vc = sv([sv([elp], 'a1i', '( %s e. %s <-> ( %s e. NN /\\ %s || P ) )' % (v, DVP, v, v)),
             sv([], 'simpr', '%s e. %s' % (v, DVP))], 'mpbid', '( %s e. NN /\\ %s || P )' % (v, v))
    return {'st': sv, 'nn': sv([vc], 'simpld', '%s e. NN' % v),
            'dP': sv([vc], 'simprd', '%s || P' % v)}


def lcmnn(w, ante, u, e, unn, enn):
    """( ante -> ( u lcm e ) e. NN ) from u, e e. NN"""
    st = mkst(w, ante)
    uz = st([unn], 'nnzd', '%s e. ZZ' % u)
    ez = st([enn], 'nnzd', '%s e. ZZ' % e)
    n1 = st([st([unn], 'nnne0d', '%s =/= 0' % u), w.inst('neneq')], 'syl', '-. %s = 0' % u)
    n2 = st([st([enn], 'nnne0d', '%s =/= 0' % e), w.inst('neneq')], 'syl', '-. %s = 0' % e)
    nor = st([st([n1, n2], 'jca', '( -. %s = 0 /\\ -. %s = 0 )' % (u, e)),
              w.s([], 'ioran', '( -. ( %s = 0 \\/ %s = 0 ) <-> ( -. %s = 0 /\\ -. %s = 0 ) )'
                   % (u, e, u, e))],
             'sylibr', '-. ( %s = 0 \\/ %s = 0 )' % (u, e))
    return st([st([uz, ez], 'jca', '( %s e. ZZ /\\ %s e. ZZ )' % (u, e)), nor,
               w.inst('lcmn0cl')], 'syl2anc', '( %s lcm %s ) e. NN' % (u, e))


def indvp(w, ante, E, nn, dP, y='x'):
    """( ante -> E e. DV ( P ) ) from steps proving E e. NN and E || P"""
    DVP = DV('P', y)
    st = mkst(w, ante)
    el = w.s([w.s([], 'breq1', '( %s = %s -> ( %s || P <-> %s || P ) )' % (y, E, y, E))], 'elrab',
             '( %s e. %s <-> ( %s e. NN /\\ %s || P ) )' % (E, DVP, E, E))
    return st([st([nn, dP], 'jca', '( %s e. NN /\\ %s || P )' % (E, E)),
               st([st([el], 'a1i', '( %s e. %s <-> ( %s e. NN /\\ %s || P ) )' % (E, DVP, E, E))],
                  'biimprd', '( ( %s e. NN /\\ %s || P ) -> %s e. %s )' % (E, E, E, DVP))],
              'mpd', '%s e. %s' % (E, DVP))


def dvpel2(w, AV, j, k, y='x'):
    """Facts about `( j e. DV ( P ) /\\ k e. DV ( P ) )` under
    `AV = ( A /\\ ( j e. DV ( P ) /\\ k e. DV ( P ) ) )`."""
    DVP = DV('P', y)
    sv = mkst(w, AV)
    pr = sv([], 'simpr', '( %s e. %s /\\ %s e. %s )' % (j, DVP, k, DVP))
    out = {'st': sv}
    for v, ref in ((j, 'simpld'), (k, 'simprd')):
        mem = sv([pr], ref, '%s e. %s' % (v, DVP))
        el = w.s([w.s([], 'breq1', '( %s = %s -> ( %s || P <-> %s || P ) )' % (y, v, y, v))],
                 'elrab', '( %s e. %s <-> ( %s e. NN /\\ %s || P ) )' % (v, DVP, v, v))
        c = sv([sv([el], 'a1i',
                    '( %s e. %s <-> ( %s e. NN /\\ %s || P ) )' % (v, DVP, v, v)), mem],
               'mpbid', '( %s e. NN /\\ %s || P )' % (v, v))
        out[v] = {'nn': sv([c], 'simpld', '%s e. NN' % v),
                  'dP': sv([c], 'simprd', '%s || P' % v)}
    return out


def sdvfix(w, n0):
    """Rewrite the body-congruence refs of the worksheet lines added since index
    `n0` from the `( ( ph /\\ k e. A ) -> B = C )` form to the `( ph -> B = C )`
    form.  tools/congr.py emits `sumeq2dv`/`prodeq2dv`, whose hypothesis is under
    the extended antecedent; a congruence whose leaves are an equation between
    two class terms proves the hypothesis under `ph` alone."""
    for i in range(n0, len(w.lines)):
        w.lines[i] = (w.lines[i].replace(':sumeq2dv ', ':sumeq2sdv ')
                                .replace(':prodeq2dv ', ':prodeq2sdv '))
