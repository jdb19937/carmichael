"""Sortie z4c: cophrmfl (coprime_harmonic_ge' at a real argument) and phiinvpf."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from tm import W
from z4clib import STATEMENTS as S, CS, FLA, PRQ


def mk(w, a):
    return lambda hyps, ref, g, name=None: w.s(hyps, ref, '( %s -> %s )' % (a, g), name=name)


def a1(w, ante, ref, fact, hyps=()):
    return w.s([w.s(list(hyps), ref, fact)], 'a1i', '( %s -> %s )' % (ante, fact))


def cophrmfl():
    w = W('cophrmfl', "The coprime harmonic bound at a real argument (Lean coprime_harmonic_ge'): "
          '( phi ( K ) / K ) log A is at most the sum of 1 / j over j <_ A coprime to K.')
    AA = '( K e. NN /\\ A e. RR /\\ 1 <_ A )'
    st = mk(w, AA)
    CSA = CS('K', FLA)
    HARM = 'sum_ m e. ( 1 ... %s ) ( 1 / m )' % FLA
    SCOP = 'sum_ j e. %s ( 1 / j )' % CSA
    KPHI = '( K / ( phi ` K ) )'
    PHIK = '( ( phi ` K ) / K )'
    knn = st([], 'simp1', 'K e. NN')
    are = st([], 'simp2', 'A e. RR')
    a1le = st([], 'simp3', '1 <_ A')
    wnn = st([are, a1le, w.inst('flge1nn')], 'syl2anc', '%s e. NN' % FLA)
    apos = st([st([], '0red', '0 e. RR'), st([], '1red', '1 e. RR'), are,
               a1(w, AA, '0lt1', '0 < 1'), a1le], 'ltletrd', '0 < A')
    arp = st([are, apos], 'elrpd', 'A e. RR+')
    hl = st([arp, w.inst('harmoniclbnd')], 'syl', '( log ` A ) <_ %s' % HARM)
    ch = st([knn, wnn, w.inst('cophrmh')], 'syl2anc', '%s <_ ( %s x. %s )' % (HARM, KPHI, SCOP))
    logre = st([arp], 'relogcld', '( log ` A ) e. RR')
    fzfin = st([], 'fzfid', '( 1 ... %s ) e. Fin' % FLA)
    AM = '( %s /\\ m e. ( 1 ... %s ) )' % (AA, FLA)
    sm = mk(w, AM)
    mrp = sm([sm([sm([sm([], 'simpr', 'm e. ( 1 ... %s )' % FLA), w.inst('elfznn')], 'syl', 'm e. NN')],
                 'nnrpd', 'm e. RR+')], 'rpreccld', '( 1 / m ) e. RR+')
    hre = st([fzfin, sm([mrp], 'rpred', '( 1 / m ) e. RR')], 'fsumrecl', '%s e. RR' % HARM)
    csss = a1(w, AA, 'ssrab2', '%s C_ ( 1 ... %s )' % (CSA, FLA))
    csfin = st([fzfin, csss], 'ssfid', '%s e. Fin' % CSA)
    AJ = '( %s /\\ j e. %s )' % (AA, CSA)
    sj = mk(w, AJ)
    csss2 = a1(w, AJ, 'ssrab2', '%s C_ ( 1 ... %s )' % (CSA, FLA))
    jrp = sj([sj([sj([sj([csss2, sj([], 'simpr', 'j e. %s' % CSA)], 'sseldd', 'j e. ( 1 ... %s )' % FLA),
                      w.inst('elfznn')], 'syl', 'j e. NN')], 'nnrpd', 'j e. RR+')], 'rpreccld', '( 1 / j ) e. RR+')
    scre = st([csfin, sj([jrp], 'rpred', '( 1 / j ) e. RR')], 'fsumrecl', '%s e. RR' % SCOP)
    phinn = st([knn], 'phicld', '( phi ` K ) e. NN')
    phirp = st([phinn], 'nnrpd', '( phi ` K ) e. RR+')
    krp = st([knn], 'nnrpd', 'K e. RR+')
    kphirp = st([krp, phirp], 'rpdivcld', '%s e. RR+' % KPHI)
    phikrp = st([phirp, krp], 'rpdivcld', '%s e. RR+' % PHIK)
    p2re = st([st([kphirp], 'rpred', '%s e. RR' % KPHI), scre], 'remulcld', '( %s x. %s ) e. RR' % (KPHI, SCOP))
    lt = st([logre, hre, p2re, hl, ch], 'letrd', '( log ` A ) <_ ( %s x. %s )' % (KPHI, SCOP))
    phikre = st([phikrp], 'rpred', '%s e. RR' % PHIK)
    mul = st([logre, p2re, phikre, st([phikrp], 'rpge0d', '0 <_ %s' % PHIK), lt], 'lemul2ad',
             '( %s x. ( log ` A ) ) <_ ( %s x. ( %s x. %s ) )' % (PHIK, PHIK, KPHI, SCOP))
    phic = st([phinn], 'nncnd', '( phi ` K ) e. CC')
    kc = st([knn], 'nncnd', 'K e. CC')
    one = st([phic, kc, st([phinn], 'nnne0d', '( phi ` K ) =/= 0'), st([knn], 'nnne0d', 'K =/= 0')],
             'divcan6d', '( %s x. %s ) = 1' % (PHIK, KPHI))
    scc = st([scre], 'recnd', '%s e. CC' % SCOP)
    asc = st([st([phikre], 'recnd', '%s e. CC' % PHIK), st([st([kphirp], 'rpred', '%s e. RR' % KPHI)], 'recnd', '%s e. CC' % KPHI), scc],
             'mulassd', '( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) )' % (PHIK, KPHI, SCOP, PHIK, KPHI, SCOP))
    e1 = st([st([one], 'oveq1d', '( ( %s x. %s ) x. %s ) = ( 1 x. %s )' % (PHIK, KPHI, SCOP, SCOP)),
             st([scc], 'mullidd', '( 1 x. %s ) = %s' % (SCOP, SCOP))], 'eqtrd',
            '( ( %s x. %s ) x. %s ) = %s' % (PHIK, KPHI, SCOP, SCOP))
    e2 = st([asc, e1], 'eqtr3d', '( %s x. ( %s x. %s ) ) = %s' % (PHIK, KPHI, SCOP, SCOP))
    w.qed([mul, e2], 'breqtrd', S['cophrmfl'])
    return w


def phiinvpf():
    w = W('phiinvpf', 'For a positive integer L, ( 1 / L ) times the Euler product of '
          '1 / ( 1 - 1 / q ) over the primes dividing L is 1 / phi ( L ).')
    AL = 'L e. NN'
    st = mk(w, AL)
    PF = '{ r e. Prime | r || L }'
    PF0 = '{ q e. Prime | q || L }'
    lnn = st([], 'id', AL)
    e1 = w.s([w.s([], 'breq1', '( q = r -> ( q || L <-> r || L ) )')], 'cbvrabv', '%s = %s' % (PF0, PF))
    e2 = w.s([e1], 'prodeq1i', 'prod_ p e. %s ( 1 - ( 1 / p ) ) = prod_ p e. %s ( 1 - ( 1 / p ) )' % (PF0, PF))
    e3 = w.s([w.s([w.s([], 'oveq2', '( p = q -> ( 1 / p ) = ( 1 / q ) )')], 'oveq2d',
                  '( p = q -> ( 1 - ( 1 / p ) ) = ( 1 - ( 1 / q ) ) )')], 'cbvprodv',
             'prod_ p e. %s ( 1 - ( 1 / p ) ) = prod_ q e. %s ( 1 - ( 1 / q ) )' % (PF, PF))
    e4 = w.s([e2, e3], 'eqtri', 'prod_ p e. %s ( 1 - ( 1 / p ) ) = prod_ q e. %s ( 1 - ( 1 / q ) )' % (PF0, PF))
    PH = '( ( phi ` L ) / L )'
    PP = 'prod_ q e. %s ( 1 - ( 1 / q ) )' % PF
    ph1 = st([st([lnn, w.inst('phipfprod')], 'syl', 'prod_ p e. %s ( 1 - ( 1 / p ) ) = %s' % (PF0, PH)),
              st([e4], 'a1i', 'prod_ p e. %s ( 1 - ( 1 / p ) ) = %s' % (PF0, PP))], 'eqtr3d', '%s = %s' % (PP, PH))
    pffin = st([st([lnn, w.inst('pffinq')], 'syl', '%s e. Fin' % PF0), st([e1], 'a1i', '%s = %s' % (PF0, PF))],
               'eqeltrrd', '%s e. Fin' % PF)
    AQ = '( %s /\\ q e. %s )' % (AL, PF)
    sq = mk(w, AQ)
    qprm = sq([sq([w.s([], 'ssrab2', '%s C_ Prime' % PF)], 'a1i', '%s C_ Prime' % PF),
               sq([], 'simpr', 'q e. %s' % PF)], 'sseldd', 'q e. Prime')
    qnn = sq([qprm, w.inst('prmnn')], 'syl', 'q e. NN')
    qrp = sq([qnn], 'nnrpd', 'q e. RR+')
    qre = sq([qrp], 'rpred', 'q e. RR')
    iqre = sq([sq([qrp], 'rpreccld', '( 1 / q ) e. RR+')], 'rpred', '( 1 / q ) e. RR')
    q2 = sq([sq([qprm, w.inst('prmuz2')], 'syl', 'q e. ( ZZ>= ` 2 )'), w.inst('eluzle')], 'syl', '2 <_ q')
    q1 = sq([sq([], '1red', '1 e. RR'), sq([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR'), qre,
             sq([w.s([], '1lt2', '1 < 2')], 'a1i', '1 < 2'), q2], 'ltletrd', '1 < q')
    qrc = sq([sq([sq([qre, sq([qrp], 'rpgt0d', '0 < q')], 'jca', '( q e. RR /\\ 0 < q )'), w.inst('recgt1')], 'syl',
                 '( 1 < q <-> ( 1 / q ) < 1 )'), q1], 'mpbid', '( 1 / q ) < 1')
    sub0 = sq([sq([iqre, sq([], '1red', '1 e. RR')], 'posdifd', '( ( 1 / q ) < 1 <-> 0 < ( 1 - ( 1 / q ) ) )'), qrc],
              'mpbid', '0 < ( 1 - ( 1 / q ) )')
    subre = sq([sq([], '1red', '1 e. RR'), iqre], 'resubcld', '( 1 - ( 1 / q ) ) e. RR')
    subc = sq([subre], 'recnd', '( 1 - ( 1 / q ) ) e. CC')
    subne = sq([sub0], 'gt0ne0d', '( 1 - ( 1 / q ) ) =/= 0')
    onec = sq([sq([], '1red', '1 e. RR')], 'recnd', '1 e. CC')
    fd = st([pffin, onec, subc, subne], 'fproddiv', '%s = ( prod_ q e. %s 1 / %s )' % (PRQ, PF, PP))
    p1 = st([st([pffin], 'olcd', '( %s C_ ( ZZ>= ` 1 ) \\/ %s e. Fin )' % (PF, PF)), w.inst('prod1')], 'syl',
            'prod_ q e. %s 1 = 1' % PF)
    fd2 = st([fd, st([st([p1], 'oveq1d', '( prod_ q e. %s 1 / %s ) = ( 1 / %s )' % (PF, PP, PP)),
                      st([ph1], 'oveq2d', '( 1 / %s ) = ( 1 / %s )' % (PP, PH))], 'eqtrd',
                     '( prod_ q e. %s 1 / %s ) = ( 1 / %s )' % (PF, PP, PH))], 'eqtrd', '%s = ( 1 / %s )' % (PRQ, PH))
    phinn = st([lnn], 'phicld', '( phi ` L ) e. NN')
    phic = st([phinn], 'nncnd', '( phi ` L ) e. CC')
    phine = st([phinn], 'nnne0d', '( phi ` L ) =/= 0')
    lc = st([lnn], 'nncnd', 'L e. CC')
    lne = st([lnn], 'nnne0d', 'L =/= 0')
    rd = st([phic, lc, phine, lne], 'recdivd', '( 1 / %s ) = ( L / ( phi ` L ) )' % PH)
    pv = st([fd2, rd], 'eqtrd', '%s = ( L / ( phi ` L ) )' % PRQ)
    e5 = st([pv], 'oveq2d', '( ( 1 / L ) x. %s ) = ( ( 1 / L ) x. ( L / ( phi ` L ) ) )' % PRQ)
    e6 = st([st([st([], '1red', '1 e. RR')], 'recnd', '1 e. CC'), lc, phic, lne, phine], 'dmdcan2d',
            '( ( 1 / L ) x. ( L / ( phi ` L ) ) ) = ( 1 / ( phi ` L ) )')
    w.qed([e5, e6], 'eqtrd', S['phiinvpf'])
    return w


ALL = {'cophrmfl': cophrmfl, 'phiinvpf': phiinvpf}

if __name__ == '__main__':
    for n in (sys.argv[1:] or list(ALL)):
        ALL[n]().run()
