"""Sortie v2: TotientSumSq.lean (tsqfac, tsqkey, tsqconst, totsumsq)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from tm import W
from cl import Closure
from lin import linarith

def PF(X, v='q'): return '{ %s e. Prime | %s || %s }' % (v, v, X)
def OM(X): return '( # ` %s )' % PF(X)
def PRD(X, b='p'): return 'prod_ %s e. %s %s' % (b, X, b)
def mkst(w, a):
    return lambda hyps, ref, g: w.s(hyps, ref, '( %s -> %s )' % (a, g))
def SQ3(v): return ('if ( ( mmu ` %s ) =/= 0 , ( ( 3 ^ %s ) / ( phi ` %s ) ) , 0 )'
                    % (v, OM(v), v))


def tsqfac():
    w = W('tsqfac', 'The factorwise inequality for the squared totient ratio.')
    A = 'P e. Prime'
    U = '( P - 1 )'
    st = mkst(w, A)
    pnn = st([], 'prmnn', 'P e. NN')
    pr = st([pnn], 'nnred', 'P e. RR')
    pc = st([pnn], 'nncnd', 'P e. CC')
    pne = st([pnn], 'nnne0d', 'P =/= 0')
    puz = st([], 'prmuz2', 'P e. ( ZZ>= ` 2 )')
    ez = st([w.s([], 'eluz2', '( P e. ( ZZ>= ` 2 ) <-> ( 2 e. ZZ /\\ P e. ZZ /\\ 2 <_ P ) )')],
            'a1i', '( P e. ( ZZ>= ` 2 ) <-> ( 2 e. ZZ /\\ P e. ZZ /\\ 2 <_ P ) )')
    p2 = st([st([ez, puz], 'mpbid', '( 2 e. ZZ /\\ P e. ZZ /\\ 2 <_ P )')], 'simp3d', '2 <_ P')
    one = st([], '1red', '1 e. RR')
    onec = st([], '1cnd', '1 e. CC')
    twor = st([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR')
    ur = st([pr, one], 'resubcld', '%s e. RR' % U)
    uc = st([pc, onec], 'subcld', '%s e. CC' % U)
    sub1 = st([twor, pr, one, p2], 'lesub1dd', '( 2 - 1 ) <_ %s' % U)
    e21 = st([w.s([], '2m1e1', '( 2 - 1 ) = 1')], 'a1i', '( 2 - 1 ) = 1')
    uge1 = st([e21, sub1], 'eqbrtrrd', '1 <_ %s' % U)
    zlt = st([w.s([], '0lt1', '0 < 1')], 'a1i', '0 < 1')
    zre = st([], '0red', '0 e. RR')
    upos = st([zre, one, ur, zlt, uge1], 'ltletrd', '0 < %s' % U)
    urp = st([ur, upos], 'elrpd', '%s e. RR+' % U)
    une = st([urp], 'rpne0d', '%s =/= 0' % U)
    u2rp = st([urp, urp], 'rpmulcld', '( %s x. %s ) e. RR+' % (U, U))
    sq2 = st([uc], 'sqvald', '( %s ^ 2 ) = ( %s x. %s )' % (U, U, U))
    u2rp2 = st([sq2, u2rp], 'eqeltrd', '( %s ^ 2 ) e. RR+' % U)
    # ( 1 ) the left side as a quotient of squares
    lhs = st([pc, uc, une, w.inst('sqdiv')], 'syl3anc',
             '( ( P / %s ) ^ 2 ) = ( ( P ^ 2 ) / ( %s ^ 2 ) )' % (U, U))
    # ( 2 ) the right side over the common denominator
    thr = st([w.s([], '3re', '3 e. RR')], 'a1i', '3 e. RR')
    thc = st([w.s([], '3cn', '3 e. CC')], 'a1i', '3 e. CC')
    u3c = st([uc, thc], 'addcld', '( %s + 3 ) e. CC' % U)
    dd = st([uc, thc, uc, une], 'divdird',
            '( ( %s + 3 ) / %s ) = ( ( %s / %s ) + ( 3 / %s ) )' % (U, U, U, U, U))
    dd2 = st([uc, une], 'dividd', '( %s / %s ) = 1' % (U, U))
    rhs1 = st([dd, st([dd2], 'oveq1d',
              '( ( %s / %s ) + ( 3 / %s ) ) = ( 1 + ( 3 / %s ) )' % (U, U, U, U))], 'eqtrd',
              '( ( %s + 3 ) / %s ) = ( 1 + ( 3 / %s ) )' % (U, U, U))
    ujc = st([uc, une], 'jca', '( %s e. CC /\\ %s =/= 0 )' % (U, U))
    c5 = st([u3c, ujc, ujc, w.inst('divcan5')], 'syl3anc',
            '( ( %s x. ( %s + 3 ) ) / ( %s x. %s ) ) = ( ( %s + 3 ) / %s )' % (U, U, U, U, U, U))
    rhs2 = st([st([sq2], 'oveq2d',
              '( ( %s x. ( %s + 3 ) ) / ( %s ^ 2 ) ) = ( ( %s x. ( %s + 3 ) ) / ( %s x. %s ) )'
              % (U, U, U, U, U, U, U)), c5], 'eqtrd',
              '( ( %s x. ( %s + 3 ) ) / ( %s ^ 2 ) ) = ( ( %s + 3 ) / %s )' % (U, U, U, U, U))
    rhs3 = st([rhs2, rhs1], 'eqtrd',
              '( ( %s x. ( %s + 3 ) ) / ( %s ^ 2 ) ) = ( 1 + ( 3 / %s ) )' % (U, U, U, U))
    # ( 3 ) the numerator inequality
    n1 = st([uc, uc, thc], 'adddid',
            '( %s x. ( %s + 3 ) ) = ( ( %s x. %s ) + ( %s x. 3 ) )' % (U, U, U, U, U))
    n2 = st([uc, pc, onec], 'subdird',
            '( %s x. %s ) = ( ( P x. %s ) - ( 1 x. %s ) )' % (U, U, U, U))
    n3 = st([pc, pc, onec], 'subdid', '( P x. %s ) = ( ( P x. P ) - ( P x. 1 ) )' % U)
    n4 = st([pc], 'mulridd', '( P x. 1 ) = P')
    n5 = st([n3, st([n4], 'oveq2d', '( ( P x. P ) - ( P x. 1 ) ) = ( ( P x. P ) - P )')], 'eqtrd',
            '( P x. %s ) = ( ( P x. P ) - P )' % U)
    n6 = st([uc], 'mullidd', '( 1 x. %s ) = %s' % (U, U))
    n7 = st([n2, st([n5, n6], 'oveq12d',
            '( ( P x. %s ) - ( 1 x. %s ) ) = ( ( ( P x. P ) - P ) - %s )' % (U, U, U))], 'eqtrd',
            '( %s x. %s ) = ( ( ( P x. P ) - P ) - %s )' % (U, U, U))
    n8 = st([n1, st([n7], 'oveq1d',
            '( ( %s x. %s ) + ( %s x. 3 ) ) = ( ( ( ( P x. P ) - P ) - %s ) + ( %s x. 3 ) )'
            % (U, U, U, U, U))], 'eqtrd',
            '( %s x. ( %s + 3 ) ) = ( ( ( ( P x. P ) - P ) - %s ) + ( %s x. 3 ) )' % (U, U, U, U))
    c = Closure(w, A, {'P': ('NN', pnn)})
    lin = linarith(w, A, [p2],
                   '( P x. P ) <_ ( ( ( ( P x. P ) - P ) - %s ) + ( %s x. 3 ) )' % (U, U),
                   closure=c)
    psq = st([pc], 'sqvald', '( P ^ 2 ) = ( P x. P )')
    num = st([st([psq, lin], 'eqbrtrd',
                 '( P ^ 2 ) <_ ( ( ( ( P x. P ) - P ) - %s ) + ( %s x. 3 ) )' % (U, U)),
              st([n8], 'eqcomd',
                 '( ( ( ( P x. P ) - P ) - %s ) + ( %s x. 3 ) ) = ( %s x. ( %s + 3 ) )'
                 % (U, U, U, U))], 'breqtrd', '( P ^ 2 ) <_ ( %s x. ( %s + 3 ) )' % (U, U))
    # ( 4 ) divide by ( U ^ 2 )
    p2r = st([pr, pr], 'remulcld', '( P x. P ) e. RR')
    psqr = st([psq, p2r], 'eqeltrd', '( P ^ 2 ) e. RR')
    u3r = st([ur, thr], 'readdcld', '( %s + 3 ) e. RR' % U)
    nr = st([ur, u3r], 'remulcld', '( %s x. ( %s + 3 ) ) e. RR' % (U, U))
    dvle = st([psqr, nr, u2rp2, num], 'lediv1dd',
              '( ( P ^ 2 ) / ( %s ^ 2 ) ) <_ ( ( %s x. ( %s + 3 ) ) / ( %s ^ 2 ) )' % (U, U, U, U))
    r1 = st([lhs, dvle], 'eqbrtrd',
            '( ( P / %s ) ^ 2 ) <_ ( ( %s x. ( %s + 3 ) ) / ( %s ^ 2 ) )' % (U, U, U, U))
    w.qed([r1, rhs3], 'breqtrd', '( %s -> ( ( P / %s ) ^ 2 ) <_ ( 1 + ( 3 / %s ) ) )' % (A, U, U))
    return w


G3 = '( t e. Prime |-> ( 3 / ( t - 1 ) ) )'
DVM = '{ x e. NN | x || M }'
SDM = '{ x e. NN | ( ( mmu ` x ) =/= 0 /\\ x || M ) }'


def pclos3(w, f, v, prm):
    """closures for a prime v: returns a dict"""
    pnn = f([prm, w.inst('prmnn')], 'syl', '%s e. NN' % v)
    pc = f([pnn], 'nncnd', '%s e. CC' % v)
    pr = f([pnn], 'nnred', '%s e. RR' % v)
    pne = f([pnn], 'nnne0d', '%s =/= 0' % v)
    puz = f([prm, w.inst('prmuz2')], 'syl', '%s e. ( ZZ>= ` 2 )' % v)
    pm1rp = f([puz, w.inst('uz2m1rp')], 'syl', '( %s x. ( %s - 1 ) ) e. RR+' % (v, v))
    onec = f([], '1cnd', '1 e. CC')
    oner = f([], '1red', '1 e. RR')
    p1c = f([pc, onec], 'subcld', '( %s - 1 ) e. CC' % v)
    p1r = f([pr, oner], 'resubcld', '( %s - 1 ) e. RR' % v)
    mne = f([pm1rp], 'rpne0d', '( %s x. ( %s - 1 ) ) =/= 0' % (v, v))
    p1ne = f([pc, p1c, mne], 'mulne0bbd', '( %s - 1 ) =/= 0' % v)
    prp = f([pnn], 'nnrpd', '%s e. RR+' % v)
    dvq = f([pm1rp, prp], 'rpdivcld', '( ( %s x. ( %s - 1 ) ) / %s ) e. RR+' % (v, v, v))
    can = f([p1c, pc, pne], 'divcan3d', '( ( %s x. ( %s - 1 ) ) / %s ) = ( %s - 1 )' % (v, v, v, v))
    p1rp = f([can, dvq], 'eqeltrrd', '( %s - 1 ) e. RR+' % v)
    return dict(pnn=pnn, pc=pc, pr=pr, pne=pne, p1c=p1c, p1r=p1r, p1ne=p1ne, onec=onec, oner=oner,
                prp=prp, pm1rp=pm1rp, p1rp=p1rp)


def tsqtrm():
    w = W('tsqtrm', 'Three to the number of prime factors over the totient, as a product.')
    A = '( D e. NN /\\ ( mmu ` D ) =/= 0 )'
    T = PF('D')
    PP1 = 'prod_ p e. %s ( p - 1 )' % T
    PR = 'prod_ p e. %s ( 3 / ( p - 1 ) )' % T
    st = mkst(w, A)
    d = st([], 'simpl', 'D e. NN')
    finp = st([d, w.inst('prmdvdsfi')], 'syl', '%s e. Fin' % PF('D', 'p'))
    cbv = st([w.s([], 'cbvrabv', '%s = %s' % (PF('D', 'p'), T))], 'a1i',
             '%s = %s' % (PF('D', 'p'), T))
    fin = st([cbv, finp], 'eqeltrrd', '%s e. Fin' % T)
    CP = '( %s /\\ p e. %s )' % (A, T)
    fp = mkst(w, CP)
    pprm = fp([fp([], 'simpr', 'p e. %s' % T), w.inst('elrabi')], 'syl', 'p e. Prime')
    c = pclos3(w, fp, 'p', pprm)
    thc = fp([w.s([], '3cn', '3 e. CC')], 'a1i', '3 e. CC')
    dv = st([fin, thc, c['p1c'], c['p1ne']], 'fproddiv',
            '%s = ( prod_ p e. %s 3 / %s )' % (PR, T, PP1))
    thc2 = st([w.s([], '3cn', '3 e. CC')], 'a1i', '3 e. CC')
    cst = st([fin, thc2, w.inst('fprodconst')], 'syl2anc',
             'prod_ p e. %s 3 = ( 3 ^ %s )' % (T, OM('D')))
    phs = st([], 'phisqf', '( phi ` D ) = %s' % PP1)
    w.qed([dv, st([cst, st([phs], 'eqcomd', '%s = ( phi ` D )' % PP1)], 'oveq12d',
          '( prod_ p e. %s 3 / %s ) = ( ( 3 ^ %s ) / ( phi ` D ) )' % (T, PP1, OM('D')))], 'eqtrd',
          '( %s -> %s = ( ( 3 ^ %s ) / ( phi ` D ) ) )' % (A, PR, OM('D')))
    return w


def tsqkey():
    w = W('tsqkey',
          'The square of M over its totient is at most the divisor sum of three to the number of '
          'prime factors over the totient.')
    A = 'M e. NN'
    T = PF('M')
    PA = 'prod_ p e. %s ( p / ( p - 1 ) )' % T
    PS = 'prod_ p e. %s ( ( p / ( p - 1 ) ) ^ 2 )' % T
    PG = 'prod_ p e. %s ( 1 + ( %s ` p ) )' % (T, G3)
    S1 = 'sum_ d e. %s prod_ p e. %s ( %s ` p )' % (SDM, PF('d'), G3)
    S2 = 'sum_ d e. %s %s' % (SDM, SQ3('d'))
    S3 = 'sum_ d e. %s %s' % (DVM, SQ3('d'))
    st = mkst(w, A)
    m = w.s([], 'id', '( %s -> M e. NN )' % A)
    finM = st([m, w.inst('dvdsfi')], 'syl', '%s e. Fin' % DVM)
    finp = st([m, w.inst('prmdvdsfi')], 'syl', '%s e. Fin' % PF('M', 'p'))
    cbv = st([w.s([], 'cbvrabv', '%s = %s' % (PF('M', 'p'), T))], 'a1i',
             '%s = %s' % (PF('M', 'p'), T))
    fin = st([cbv, finp], 'eqeltrrd', '%s e. Fin' % T)
    # G3 : Prime --> CC
    gf1 = w.s([], 'eqid', '%s = %s' % (G3, G3))
    CT = '( %s /\\ t e. Prime )' % A
    ft = mkst(w, CT)
    ct = pclos3(w, ft, 't', ft([], 'simpr', 't e. Prime'))
    thct = ft([w.s([], '3cn', '3 e. CC')], 'a1i', '3 e. CC')
    gcl = ft([thct, ct['p1c'], ct['p1ne']], 'divcld', '( 3 / ( t - 1 ) ) e. CC')
    gfn = st([gcl, gf1], 'fmptd', '%s : Prime --> CC' % G3)
    gsub = w.s([w.s([], 'oveq1', '( t = p -> ( t - 1 ) = ( p - 1 ) )')], 'oveq2d',
               '( t = p -> ( 3 / ( t - 1 ) ) = ( 3 / ( p - 1 ) ) )')
    gv = w.s([gsub, gf1], 'fvmptg',
             '( ( p e. Prime /\\ ( 3 / ( p - 1 ) ) e. _V ) -> ( %s ` p ) = ( 3 / ( p - 1 ) ) )' % G3)
    # ( 1 ) the square of the product
    CP = '( %s /\\ p e. %s )' % (A, T)
    fp = mkst(w, CP)
    pprm = fp([fp([], 'simpr', 'p e. %s' % T), w.inst('elrabi')], 'syl', 'p e. Prime')
    c = pclos3(w, fp, 'p', pprm)
    xc = fp([c['pc'], c['p1c'], c['p1ne']], 'divcld', '( p / ( p - 1 ) ) e. CC')
    sq1 = st([fin, xc, xc], 'fprodmul', 'prod_ p e. %s ( ( p / ( p - 1 ) ) x. ( p / ( p - 1 ) ) ) = ( %s x. %s )'
             % (T, PA, PA))
    pac = st([fin, xc], 'fprodcl', '%s e. CC' % PA)
    sq2 = st([pac], 'sqvald', '( %s ^ 2 ) = ( %s x. %s )' % (PA, PA, PA))
    sq3 = st([fp([xc], 'sqvald',
                 '( ( p / ( p - 1 ) ) ^ 2 ) = ( ( p / ( p - 1 ) ) x. ( p / ( p - 1 ) ) )')],
             'prodeq2dv',
             '%s = prod_ p e. %s ( ( p / ( p - 1 ) ) x. ( p / ( p - 1 ) ) )' % (PS, T))
    sq4 = st([st([sq3, sq1], 'eqtrd', '%s = ( %s x. %s )' % (PS, PA, PA)),
              st([sq2], 'eqcomd', '( %s x. %s ) = ( %s ^ 2 )' % (PA, PA, PA))], 'eqtrd',
             '%s = ( %s ^ 2 )' % (PS, PA))
    pr = st([], 'phirad', '( M / ( phi ` M ) ) = %s' % PA)
    lhs = st([st([pr], 'oveq1d', '( ( M / ( phi ` M ) ) ^ 2 ) = ( %s ^ 2 )' % PA),
              st([sq4], 'eqcomd', '( %s ^ 2 ) = %s' % (PA, PS))], 'eqtrd',
             '( ( M / ( phi ` M ) ) ^ 2 ) = %s' % PS)
    # ( 2 ) the factorwise bound
    xrp = fp([c['prp'], c['p1rp']], 'rpdivcld', '( p / ( p - 1 ) ) e. RR+')
    xr = fp([xrp], 'rpred', '( p / ( p - 1 ) ) e. RR')
    xsqr = fp([xr], 'resqcld', '( ( p / ( p - 1 ) ) ^ 2 ) e. RR')
    xsq0 = fp([xr], 'sqge0d', '0 <_ ( ( p / ( p - 1 ) ) ^ 2 )')
    thcp = fp([w.s([], '3cn', '3 e. CC')], 'a1i', '3 e. CC')
    thrp = fp([w.s([], '3re', '3 e. RR')], 'a1i', '3 e. RR')
    gclp = fp([thcp, c['p1c'], c['p1ne']], 'divcld', '( 3 / ( p - 1 ) ) e. CC')
    gexp = fp([gclp, w.inst('elex')], 'syl', '( 3 / ( p - 1 ) ) e. _V')
    gvp = fp([pprm, gexp, gv], 'syl2anc', '( %s ` p ) = ( 3 / ( p - 1 ) )' % G3)
    grp = fp([thrp, c['p1rp']], 'rerpdivcld', '( 3 / ( p - 1 ) ) e. RR')
    gr = fp([gvp, grp], 'eqeltrd', '( %s ` p ) e. RR' % G3)
    bdr = fp([c['oner'], gr], 'readdcld', '( 1 + ( %s ` p ) ) e. RR' % G3)
    fac = fp([pprm, w.inst('tsqfac')], 'syl',
             '( ( p / ( p - 1 ) ) ^ 2 ) <_ ( 1 + ( 3 / ( p - 1 ) ) )')
    fac2 = fp([fac, fp([fp([gvp], 'oveq2d',
              '( 1 + ( %s ` p ) ) = ( 1 + ( 3 / ( p - 1 ) ) )' % G3)], 'eqcomd',
              '( 1 + ( 3 / ( p - 1 ) ) ) = ( 1 + ( %s ` p ) )' % G3)], 'breqtrd',
              '( ( p / ( p - 1 ) ) ^ 2 ) <_ ( 1 + ( %s ` p ) )' % G3)
    nf = w.s([], 'nfv', 'F/ p %s' % A)
    ple = st([nf, fin, xsqr, xsq0, bdr, fac2], 'fprodle', '%s <_ %s' % (PS, PG))
    # ( 3 ) the master identity and the termwise evaluation
    key = st([m, gfn, w.inst('sqfdvdsum')], 'syl2anc', '%s = %s' % (S1, PG))
    elsd = w.s([w.s([w.s([w.s([], 'fveq2', '( x = d -> ( mmu ` x ) = ( mmu ` d ) )')], 'neeq1d',
                         '( x = d -> ( ( mmu ` x ) =/= 0 <-> ( mmu ` d ) =/= 0 ) )'),
                     w.s([], 'breq1', '( x = d -> ( x || M <-> d || M ) )')], 'anbi12d',
                    '( x = d -> ( ( ( mmu ` x ) =/= 0 /\\ x || M ) <-> ( ( mmu ` d ) =/= 0 /\\ d || M ) ) )')],
               'elrab', '( d e. %s <-> ( d e. NN /\\ ( ( mmu ` d ) =/= 0 /\\ d || M ) ) )' % SDM)
    CD = '( %s /\\ d e. %s )' % (A, SDM)
    fd = mkst(w, CD)
    din = fd([], 'simpr', 'd e. %s' % SDM)
    dfacts = fd([fd([elsd], 'a1i',
                    '( d e. %s <-> ( d e. NN /\\ ( ( mmu ` d ) =/= 0 /\\ d || M ) ) )' % SDM), din],
                'mpbid', '( d e. NN /\\ ( ( mmu ` d ) =/= 0 /\\ d || M ) )')
    dnn = fd([dfacts], 'simpld', 'd e. NN')
    dsq = fd([fd([dfacts], 'simprd', '( ( mmu ` d ) =/= 0 /\\ d || M )')], 'simpld',
             '( mmu ` d ) =/= 0')
    CDP = '( %s /\\ p e. %s )' % (CD, PF('d'))
    fdp = mkst(w, CDP)
    pprmd = fdp([fdp([], 'simpr', 'p e. %s' % PF('d')), w.inst('elrabi')], 'syl', 'p e. Prime')
    cd = pclos3(w, fdp, 'p', pprmd)
    thcd = fdp([w.s([], '3cn', '3 e. CC')], 'a1i', '3 e. CC')
    gcld = fdp([thcd, cd['p1c'], cd['p1ne']], 'divcld', '( 3 / ( p - 1 ) ) e. CC')
    gexd = fdp([gcld, w.inst('elex')], 'syl', '( 3 / ( p - 1 ) ) e. _V')
    gvd = fdp([pprmd, gexd, gv], 'syl2anc', '( %s ` p ) = ( 3 / ( p - 1 ) )' % G3)
    prdd = fd([gvd], 'prodeq2dv',
              'prod_ p e. %s ( %s ` p ) = prod_ p e. %s ( 3 / ( p - 1 ) )' % (PF('d'), G3, PF('d')))
    trm = fd([fd([dnn, dsq], 'jca', '( d e. NN /\\ ( mmu ` d ) =/= 0 )'), w.inst('tsqtrm')], 'syl',
             'prod_ p e. %s ( 3 / ( p - 1 ) ) = ( ( 3 ^ %s ) / ( phi ` d ) )' % (PF('d'), OM('d')))
    iftr = fd([dsq], 'iftrued', '%s = ( ( 3 ^ %s ) / ( phi ` d ) )' % (SQ3('d'), OM('d')))
    term = fd([fd([prdd, trm], 'eqtrd',
                  'prod_ p e. %s ( %s ` p ) = ( ( 3 ^ %s ) / ( phi ` d ) )' % (PF('d'), G3, OM('d'))),
               fd([iftr], 'eqcomd', '( ( 3 ^ %s ) / ( phi ` d ) ) = %s' % (OM('d'), SQ3('d')))],
              'eqtrd', 'prod_ p e. %s ( %s ` p ) = %s' % (PF('d'), G3, SQ3('d')))
    e1 = st([term], 'sumeq2dv', '%s = %s' % (S1, S2))
    # ( 4 ) extend to all divisors
    ssi = w.s([w.s([], 'simpr', '( ( ( mmu ` x ) =/= 0 /\\ x || M ) -> x || M )')], 'a1i',
              '( x e. NN -> ( ( ( mmu ` x ) =/= 0 /\\ x || M ) -> x || M ) )')
    sss = st([w.s([ssi], 'ss2rabi', '%s C_ %s' % (SDM, DVM))], 'a1i', '%s C_ %s' % (SDM, DVM))
    omfd = fd([fd([w.s([], 'cbvrabv', '%s = %s' % (PF('d', 'p'), PF('d')))], 'a1i',
                  '%s = %s' % (PF('d', 'p'), PF('d'))),
               fd([dnn, w.inst('prmdvdsfi')], 'syl', '%s e. Fin' % PF('d', 'p'))],
              'eqeltrrd', '%s e. Fin' % PF('d'))
    hcld = fd([omfd, w.inst('hashcl')], 'syl', '%s e. NN0' % OM('d'))
    thcc = fd([w.s([], '3cn', '3 e. CC')], 'a1i', '3 e. CC')
    excd = fd([thcc, hcld], 'expcld', '( 3 ^ %s ) e. CC' % OM('d'))
    phnd = fd([dnn, w.inst('phicl')], 'syl', '( phi ` d ) e. NN')
    phcd = fd([phnd], 'nncnd', '( phi ` d ) e. CC')
    phned = fd([phnd], 'nnne0d', '( phi ` d ) =/= 0')
    qcd = fd([excd, phcd, phned], 'divcld', '( ( 3 ^ %s ) / ( phi ` d ) ) e. CC' % OM('d'))
    zcd = fd([], '0cnd', '0 e. CC')
    ifcd = fd([qcd, zcd], 'ifcld', '%s e. CC' % SQ3('d'))
    CDF = '( %s /\\ d e. ( %s \\ %s ) )' % (A, DVM, SDM)
    fdf = mkst(w, CDF)
    ddif = fdf([], 'simpr', 'd e. ( %s \\ %s )' % (DVM, SDM))
    ddv = fdf([ddif, w.inst('eldifi')], 'syl', 'd e. %s' % DVM)
    dnnf = fdf([ddv, w.inst('elrabi')], 'syl', 'd e. NN')
    dnsd = fdf([ddif, w.inst('eldifn')], 'syl', '-. d e. %s' % SDM)
    dvdf = fdf([fdf([w.s([w.s([], 'breq1', '( x = d -> ( x || M <-> d || M ) )')], 'elrab',
                        '( d e. %s <-> ( d e. NN /\\ d || M ) )' % DVM)], 'a1i',
                    '( d e. %s <-> ( d e. NN /\\ d || M ) )' % DVM), ddv], 'mpbid',
               '( d e. NN /\\ d || M )')
    dvdf2 = fdf([dvdf], 'simprd', 'd || M')
    nsq = fdf([fdf([elsd], 'a1i',
                   '( d e. %s <-> ( d e. NN /\\ ( ( mmu ` d ) =/= 0 /\\ d || M ) ) )' % SDM), dnsd],
              'mtbid', '-. ( d e. NN /\\ ( ( mmu ` d ) =/= 0 /\\ d || M ) )')
    CJ = '( %s /\\ ( mmu ` d ) =/= 0 )' % CDF
    jcs = w.s([w.s([dnnf], 'adantr', '( %s -> d e. NN )' % CJ),
               w.s([w.s([], 'simpr', '( %s -> ( mmu ` d ) =/= 0 )' % CJ),
                    w.s([dvdf2], 'adantr', '( %s -> d || M )' % CJ)], 'jca',
                   '( %s -> ( ( mmu ` d ) =/= 0 /\\ d || M ) )' % CJ)], 'jca',
              '( %s -> ( d e. NN /\\ ( ( mmu ` d ) =/= 0 /\\ d || M ) ) )' % CJ)
    mu0 = fdf([nsq, jcs], 'mtand', '-. ( mmu ` d ) =/= 0')
    vanish = fdf([mu0], 'iffalsed', '%s = 0' % SQ3('d'))
    ss = st([sss, ifcd, vanish, finM], 'fsumss', '%s = %s' % (S2, S3))
    # assemble
    a1 = st([lhs, ple], 'eqbrtrd', '( ( M / ( phi ` M ) ) ^ 2 ) <_ %s' % PG)
    a2 = st([a1, st([key], 'eqcomd', '%s = %s' % (PG, S1))], 'breqtrd',
            '( ( M / ( phi ` M ) ) ^ 2 ) <_ %s' % S1)
    a3 = st([a2, e1], 'breqtrd', '( ( M / ( phi ` M ) ) ^ 2 ) <_ %s' % S2)
    w.qed([a3, ss], 'breqtrd', '( %s -> ( ( M / ( phi ` M ) ) ^ 2 ) <_ %s )' % (A, S3))
    return w


def tsqctrm():
    w = W('tsqctrm',
          'Three to the number of prime factors over d times the totient of d, as a product.')
    A = '( D e. NN /\\ ( mmu ` D ) =/= 0 )'
    T = PF('D')
    PP = PRD(T)
    PP1 = 'prod_ p e. %s ( p - 1 )' % T
    PX = 'prod_ p e. %s ( p x. ( p - 1 ) )' % T
    PR = 'prod_ p e. %s ( 3 / ( p x. ( p - 1 ) ) )' % T
    E3 = '( 3 ^ %s )' % OM('D')
    st = mkst(w, A)
    d = st([], 'simpl', 'D e. NN')
    dc = st([d], 'nncnd', 'D e. CC')
    dne = st([d], 'nnne0d', 'D =/= 0')
    phn = st([d, w.inst('phicl')], 'syl', '( phi ` D ) e. NN')
    phc = st([phn], 'nncnd', '( phi ` D ) e. CC')
    phne = st([phn], 'nnne0d', '( phi ` D ) =/= 0')
    finp = st([d, w.inst('prmdvdsfi')], 'syl', '%s e. Fin' % PF('D', 'p'))
    cbv = st([w.s([], 'cbvrabv', '%s = %s' % (PF('D', 'p'), T))], 'a1i',
             '%s = %s' % (PF('D', 'p'), T))
    fin = st([cbv, finp], 'eqeltrrd', '%s e. Fin' % T)
    hcl = st([fin, w.inst('hashcl')], 'syl', '%s e. NN0' % OM('D'))
    thc = st([w.s([], '3cn', '3 e. CC')], 'a1i', '3 e. CC')
    e3c = st([thc, hcl], 'expcld', '%s e. CC' % E3)
    CP = '( %s /\\ p e. %s )' % (A, T)
    fp = mkst(w, CP)
    pprm = fp([fp([], 'simpr', 'p e. %s' % T), w.inst('elrabi')], 'syl', 'p e. Prime')
    c = pclos3(w, fp, 'p', pprm)
    pxc = fp([c['pc'], c['p1c']], 'mulcld', '( p x. ( p - 1 ) ) e. CC')
    pxne = fp([c['pm1rp']], 'rpne0d', '( p x. ( p - 1 ) ) =/= 0')
    thcp = fp([w.s([], '3cn', '3 e. CC')], 'a1i', '3 e. CC')
    dv = st([fin, thcp, pxc, pxne], 'fproddiv', '%s = ( prod_ p e. %s 3 / %s )' % (PR, T, PX))
    cst = st([fin, thc, w.inst('fprodconst')], 'syl2anc', 'prod_ p e. %s 3 = %s' % (T, E3))
    ml = st([fin, c['pc'], c['p1c']], 'fprodmul', '%s = ( %s x. %s )' % (PX, PP, PP1))
    pid = st([], 'sqfprodid', '%s = D' % PP)
    phs = st([], 'phisqf', '( phi ` D ) = %s' % PP1)
    ml2 = st([ml, st([pid, st([phs], 'eqcomd', '%s = ( phi ` D )' % PP1)], 'oveq12d',
             '( %s x. %s ) = ( D x. ( phi ` D ) )' % (PP, PP1))], 'eqtrd',
             '%s = ( D x. ( phi ` D ) )' % PX)
    rhs = st([dv, st([cst, ml2], 'oveq12d',
             '( prod_ p e. %s 3 / %s ) = ( %s / ( D x. ( phi ` D ) ) )' % (T, PX, E3))], 'eqtrd',
             '%s = ( %s / ( D x. ( phi ` D ) ) )' % (PR, E3))
    lhs = st([e3c, phc, phne, dc, dne], 'divdiv1d',
             '( ( %s / ( phi ` D ) ) / D ) = ( %s / ( ( phi ` D ) x. D ) )' % (E3, E3))
    cm = st([phc, dc], 'mulcomd', '( ( phi ` D ) x. D ) = ( D x. ( phi ` D ) )')
    lhs2 = st([lhs, st([cm], 'oveq2d',
              '( %s / ( ( phi ` D ) x. D ) ) = ( %s / ( D x. ( phi ` D ) ) )' % (E3, E3))], 'eqtrd',
              '( ( %s / ( phi ` D ) ) / D ) = ( %s / ( D x. ( phi ` D ) ) )' % (E3, E3))
    w.qed([lhs2, st([rhs], 'eqcomd', '( %s / ( D x. ( phi ` D ) ) ) = %s' % (E3, PR))], 'eqtrd',
          '( %s -> ( ( %s / ( phi ` D ) ) / D ) = %s )' % (A, E3, PR))
    return w


G4 = '( t e. Prime |-> ( 3 / ( t x. ( t - 1 ) ) ) )'
PM = '( ( 1 ... M ) i^i Prime )'
NR = 'prod_ r e. %s r' % PM
SDR = '{ x e. NN | ( ( mmu ` x ) =/= 0 /\\ x || %s ) }' % NR
SQM = '{ x e. ( 1 ... M ) | ( mmu ` x ) =/= 0 }'
def TERM3(v): return '( %s / %s )' % (SQ3(v), v)


def sq3clos(w, f, v, nnstep):
    """closures for SQ3 ( v ) given ( ctx -> v e. NN )"""
    omf = f([f([w.s([], 'cbvrabv', '%s = %s' % (PF(v, 'p'), PF(v)))], 'a1i',
               '%s = %s' % (PF(v, 'p'), PF(v))),
             f([nnstep, w.inst('prmdvdsfi')], 'syl', '%s e. Fin' % PF(v, 'p'))],
            'eqeltrrd', '%s e. Fin' % PF(v))
    hcl = f([omf, w.inst('hashcl')], 'syl', '%s e. NN0' % OM(v))
    thr = f([w.s([], '3re', '3 e. RR')], 'a1i', '3 e. RR')
    e3r = f([thr, hcl], 'reexpcld', '( 3 ^ %s ) e. RR' % OM(v))
    th0 = f([w.s([], '3nn0', '3 e. NN0')], 'a1i', '3 e. NN0')
    e3n0 = f([th0, hcl], 'nn0expcld', '( 3 ^ %s ) e. NN0' % OM(v))
    e3ge0 = f([e3n0], 'nn0ge0d', '0 <_ ( 3 ^ %s )' % OM(v))
    phn = f([nnstep, w.inst('phicl')], 'syl', '( phi ` %s ) e. NN' % v)
    phrp = f([phn], 'nnrpd', '( phi ` %s ) e. RR+' % v)
    q = f([e3r, phrp], 'rerpdivcld', '( ( 3 ^ %s ) / ( phi ` %s ) ) e. RR' % (OM(v), v))
    q0 = f([e3r, phrp, e3ge0], 'divge0d', '0 <_ ( ( 3 ^ %s ) / ( phi ` %s ) )' % (OM(v), v))
    zre = f([], '0red', '0 e. RR')
    ifre = f([q, zre], 'ifcld', '%s e. RR' % SQ3(v))
    b1 = w.s([], 'breq2',
             '( ( ( 3 ^ %s ) / ( phi ` %s ) ) = %s -> ( 0 <_ ( ( 3 ^ %s ) / ( phi ` %s ) ) <-> 0 <_ %s ) )'
             % (OM(v), v, SQ3(v), OM(v), v, SQ3(v)))
    b2 = w.s([], 'breq2', '( 0 = %s -> ( 0 <_ 0 <-> 0 <_ %s ) )' % (SQ3(v), SQ3(v)))
    return dict(omf=omf, hcl=hcl, q=q, q0=q0, ifre=ifre, b1=b1, b2=b2, zre=zre, phn=phn, phrp=phrp)


def tsqconst():
    w = W('tsqconst',
          'The sum of three to the number of prime factors over d times the totient of d, over the '
          'squarefree d up to M, is at most e cubed.')
    A = 'M e. NN'
    S0 = 'sum_ d e. ( 1 ... M ) %s' % TERM3('d')
    S1 = 'sum_ d e. %s %s' % (SQM, TERM3('d'))
    S2 = 'sum_ d e. %s %s' % (SDR, TERM3('d'))
    S3 = 'sum_ d e. %s prod_ p e. %s ( %s ` p )' % (SDR, PF('d'), G4)
    P1 = 'prod_ p e. %s ( 1 + ( %s ` p ) )' % (PF(NR), G4)
    P2 = 'prod_ p e. %s ( 1 + ( 3 / ( p x. ( p - 1 ) ) ) )' % PM
    st = mkst(w, A)
    m = w.s([], 'id', '( %s -> M e. NN )' % A)
    finM = st([], 'fzfid', '( 1 ... M ) e. Fin')
    finpm = st([finM, st([w.s([], 'inss1', '%s C_ ( 1 ... M )' % PM)], 'a1i',
                         '%s C_ ( 1 ... M )' % PM)], 'ssfid', '%s e. Fin' % PM)
    sspm = st([w.s([], 'inss2', '%s C_ Prime' % PM)], 'a1i', '%s C_ Prime' % PM)
    spd = st([finpm, sspm, w.inst('sqfprod')], 'syl2anc',
             '( ( %s e. NN /\\ ( mmu ` %s ) =/= 0 ) /\\ %s = %s )'
             % (PRD(PM), PRD(PM), PF(PRD(PM)), PM))
    cbp = st([w.s([w.s([], 'id', '( p = r -> p = r )')], 'cbvprodv', '%s = %s' % (PRD(PM), NR))],
             'a1i', '%s = %s' % (PRD(PM), NR))
    n12 = st([spd], 'simpld', '( %s e. NN /\\ ( mmu ` %s ) =/= 0 )' % (PRD(PM), PRD(PM)))
    nnn = st([cbp, st([n12], 'simpld', '%s e. NN' % PRD(PM))], 'eqeltrrd', '%s e. NN' % NR)
    nset = st([spd], 'simprd', '%s = %s' % (PF(PRD(PM)), PM))
    nset2 = st([st([st([cbp], 'breq2d', '( q || %s <-> q || %s )' % (PRD(PM), NR))], 'rabbidv',
                   '%s = %s' % (PF(PRD(PM)), PF(NR))), nset], 'eqtr3d', '%s = %s' % (PF(NR), PM))
    finsd = st([st([nnn, w.inst('dvdsfi')], 'syl', '{ x e. NN | x || %s } e. Fin' % NR),
                st([w.s([w.s([w.s([], 'simpr',
                   '( ( ( mmu ` x ) =/= 0 /\\ x || %s ) -> x || %s )' % (NR, NR))], 'a1i',
                   '( x e. NN -> ( ( ( mmu ` x ) =/= 0 /\\ x || %s ) -> x || %s ) )' % (NR, NR))],
                   'ss2rabi', '%s C_ { x e. NN | x || %s }' % (SDR, NR))], 'a1i',
                   '%s C_ { x e. NN | x || %s }' % (SDR, NR))], 'ssfid', '%s e. Fin' % SDR)
    # G4 : Prime --> CC
    gf1 = w.s([], 'eqid', '%s = %s' % (G4, G4))
    CT = '( %s /\\ t e. Prime )' % A
    ft = mkst(w, CT)
    ct = pclos3(w, ft, 't', ft([], 'simpr', 't e. Prime'))
    txc = ft([ct['pc'], ct['p1c']], 'mulcld', '( t x. ( t - 1 ) ) e. CC')
    txne = ft([ct['pm1rp']], 'rpne0d', '( t x. ( t - 1 ) ) =/= 0')
    thct = ft([w.s([], '3cn', '3 e. CC')], 'a1i', '3 e. CC')
    gcl = ft([thct, txc, txne], 'divcld', '( 3 / ( t x. ( t - 1 ) ) ) e. CC')
    gfn = st([gcl, gf1], 'fmptd', '%s : Prime --> CC' % G4)
    gsub1 = w.s([], 'id', '( t = p -> t = p )')
    gsub2 = w.s([], 'oveq1', '( t = p -> ( t - 1 ) = ( p - 1 ) )')
    gsub3 = w.s([gsub1, gsub2], 'oveq12d', '( t = p -> ( t x. ( t - 1 ) ) = ( p x. ( p - 1 ) ) )')
    gsub4 = w.s([gsub3], 'oveq2d',
                '( t = p -> ( 3 / ( t x. ( t - 1 ) ) ) = ( 3 / ( p x. ( p - 1 ) ) ) )')
    gv = w.s([gsub4, gf1], 'fvmptg',
             '( ( p e. Prime /\\ ( 3 / ( p x. ( p - 1 ) ) ) e. _V ) -> ( %s ` p ) = ( 3 / ( p x. ( p - 1 ) ) ) )'
             % G4)
    key = st([nnn, gfn, w.inst('sqfdvdsum')], 'syl2anc', '%s = %s' % (S3, P1))
    # the termwise identity on the squarefree divisors of NR
    elsdr = w.s([w.s([w.s([w.s([], 'fveq2', '( x = d -> ( mmu ` x ) = ( mmu ` d ) )')], 'neeq1d',
                          '( x = d -> ( ( mmu ` x ) =/= 0 <-> ( mmu ` d ) =/= 0 ) )'),
                      w.s([], 'breq1', '( x = d -> ( x || %s <-> d || %s ) )' % (NR, NR))], 'anbi12d',
                     '( x = d -> ( ( ( mmu ` x ) =/= 0 /\\ x || %s ) <-> ( ( mmu ` d ) =/= 0 /\\ d || %s ) ) )'
                     % (NR, NR))], 'elrab',
                '( d e. %s <-> ( d e. NN /\\ ( ( mmu ` d ) =/= 0 /\\ d || %s ) ) )' % (SDR, NR))
    CD = '( %s /\\ d e. %s )' % (A, SDR)
    fd = mkst(w, CD)
    din = fd([], 'simpr', 'd e. %s' % SDR)
    dfacts = fd([fd([elsdr], 'a1i',
                    '( d e. %s <-> ( d e. NN /\\ ( ( mmu ` d ) =/= 0 /\\ d || %s ) ) )' % (SDR, NR)),
                 din], 'mpbid', '( d e. NN /\\ ( ( mmu ` d ) =/= 0 /\\ d || %s ) )' % NR)
    dnn = fd([dfacts], 'simpld', 'd e. NN')
    dsq = fd([fd([dfacts], 'simprd', '( ( mmu ` d ) =/= 0 /\\ d || %s )' % NR)], 'simpld',
             '( mmu ` d ) =/= 0')
    iftr = fd([dsq], 'iftrued', '%s = ( ( 3 ^ %s ) / ( phi ` d ) )' % (SQ3('d'), OM('d')))
    lhsd = fd([iftr], 'oveq1d', '%s = ( ( ( 3 ^ %s ) / ( phi ` d ) ) / d )' % (TERM3('d'), OM('d')))
    trm = fd([fd([dnn, dsq], 'jca', '( d e. NN /\\ ( mmu ` d ) =/= 0 )'), w.inst('tsqctrm')], 'syl',
             '( ( ( 3 ^ %s ) / ( phi ` d ) ) / d ) = prod_ p e. %s ( 3 / ( p x. ( p - 1 ) ) )'
             % (OM('d'), PF('d')))
    CDP = '( %s /\\ p e. %s )' % (CD, PF('d'))
    fdp = mkst(w, CDP)
    pprmd = fdp([fdp([], 'simpr', 'p e. %s' % PF('d')), w.inst('elrabi')], 'syl', 'p e. Prime')
    cdp = pclos3(w, fdp, 'p', pprmd)
    pxcd = fdp([cdp['pc'], cdp['p1c']], 'mulcld', '( p x. ( p - 1 ) ) e. CC')
    pxned = fdp([cdp['pm1rp']], 'rpne0d', '( p x. ( p - 1 ) ) =/= 0')
    thcd = fdp([w.s([], '3cn', '3 e. CC')], 'a1i', '3 e. CC')
    gexd = fdp([fdp([thcd, pxcd, pxned], 'divcld', '( 3 / ( p x. ( p - 1 ) ) ) e. CC'),
                w.inst('elex')], 'syl', '( 3 / ( p x. ( p - 1 ) ) ) e. _V')
    gvd = fdp([pprmd, gexd, gv], 'syl2anc', '( %s ` p ) = ( 3 / ( p x. ( p - 1 ) ) )' % G4)
    prdd = fd([gvd], 'prodeq2dv',
              'prod_ p e. %s ( %s ` p ) = prod_ p e. %s ( 3 / ( p x. ( p - 1 ) ) )'
              % (PF('d'), G4, PF('d')))
    term = fd([fd([lhsd, trm], 'eqtrd',
                  '%s = prod_ p e. %s ( 3 / ( p x. ( p - 1 ) ) )' % (TERM3('d'), PF('d'))),
               fd([prdd], 'eqcomd',
                  'prod_ p e. %s ( 3 / ( p x. ( p - 1 ) ) ) = prod_ p e. %s ( %s ` p )'
                  % (PF('d'), PF('d'), G4))], 'eqtrd',
              '%s = prod_ p e. %s ( %s ` p )' % (TERM3('d'), PF('d'), G4))
    e1 = st([term], 'sumeq2dv', '%s = %s' % (S2, S3))
    # closures of the summand on SDR
    cs = sq3clos(w, fd, 'd', dnn)
    drpd = fd([dnn], 'nnrpd', 'd e. RR+')
    trmre = fd([cs['ifre'], drpd], 'rerpdivcld', '%s e. RR' % TERM3('d'))
    hh3 = w.s([cs['q0']], 'adantr',
              '( ( %s /\\ ( mmu ` d ) =/= 0 ) -> 0 <_ ( ( 3 ^ %s ) / ( phi ` d ) ) )'
              % (CD, OM('d')))
    hh4 = w.s([fd([cs['zre']], 'leidd', '0 <_ 0')], 'adantr',
              '( ( %s /\\ -. ( mmu ` d ) =/= 0 ) -> 0 <_ 0 )' % CD)
    if0 = fd([cs['b1'], cs['b2'], hh3, hh4], 'ifbothda', '0 <_ %s' % SQ3('d'))
    trm0 = fd([cs['ifre'], drpd, if0], 'divge0d', '0 <_ %s' % TERM3('d'))
    # SQM C_ SDR
    CQ = '( %s /\\ d e. %s )' % (A, SQM)
    fqm = mkst(w, CQ)
    dsqm = fqm([], 'simpr', 'd e. %s' % SQM)
    elsqm = w.s([w.s([w.s([], 'fveq2', '( x = d -> ( mmu ` x ) = ( mmu ` d ) )')], 'neeq1d',
                     '( x = d -> ( ( mmu ` x ) =/= 0 <-> ( mmu ` d ) =/= 0 ) )')], 'elrab',
                '( d e. %s <-> ( d e. ( 1 ... M ) /\\ ( mmu ` d ) =/= 0 ) )' % SQM)
    qf = fqm([fqm([elsqm], 'a1i',
                  '( d e. %s <-> ( d e. ( 1 ... M ) /\\ ( mmu ` d ) =/= 0 ) )' % SQM), dsqm],
             'mpbid', '( d e. ( 1 ... M ) /\\ ( mmu ` d ) =/= 0 )')
    qfz = fqm([qf], 'simpld', 'd e. ( 1 ... M )')
    qsq = fqm([qf], 'simprd', '( mmu ` d ) =/= 0')
    qnn = fqm([qfz, w.inst('elfznn')], 'syl', 'd e. NN')
    qdv = fqm([fqm([fqm([fqm([m], 'adantr', 'M e. NN'), qfz], 'jca',
                        '( M e. NN /\\ d e. ( 1 ... M ) )'), qsq], 'jca',
                   '( ( M e. NN /\\ d e. ( 1 ... M ) ) /\\ ( mmu ` d ) =/= 0 )'),
               w.inst('sqfdvdprod')], 'syl', 'd || %s' % PRD(PM))
    qdv2 = fqm([qdv, fqm([cbp], 'adantr', '%s = %s' % (PRD(PM), NR))], 'breqtrd', 'd || %s' % NR)
    qsdr = fqm([fqm([elsdr], 'a1i',
                    '( d e. %s <-> ( d e. NN /\\ ( ( mmu ` d ) =/= 0 /\\ d || %s ) ) )' % (SDR, NR)),
                fqm([qnn, fqm([qsq, qdv2], 'jca', '( ( mmu ` d ) =/= 0 /\\ d || %s )' % NR)], 'jca',
                    '( d e. NN /\\ ( ( mmu ` d ) =/= 0 /\\ d || %s ) )' % NR)], 'mpbird',
               'd e. %s' % SDR)
    sqmss = st([w.s([qsdr], 'ex', '( %s -> ( d e. %s -> d e. %s ) )' % (A, SQM, SDR))], 'ssrdv',
               '%s C_ %s' % (SQM, SDR))
    less = st([finsd, trmre, trm0, sqmss], 'fsumless', '%s <_ %s' % (S1, S2))
    # the sum over ( 1 ... M ) restricted to the squarefree part
    ssm = st([w.s([], 'ssrab2', '%s C_ ( 1 ... M )' % SQM)], 'a1i', '%s C_ ( 1 ... M )' % SQM)
    csq = sq3clos(w, fqm, 'd', qnn)
    drpq = fqm([qnn], 'nnrpd', 'd e. RR+')
    trmq = fqm([csq['ifre'], drpq], 'rerpdivcld', '%s e. RR' % TERM3('d'))
    trmcq = fqm([trmq], 'recnd', '%s e. CC' % TERM3('d'))
    CQD = '( %s /\\ d e. ( ( 1 ... M ) \\ %s ) )' % (A, SQM)
    fqd = mkst(w, CQD)
    ddif = fqd([], 'simpr', 'd e. ( ( 1 ... M ) \\ %s )' % SQM)
    dfzq = fqd([ddif, w.inst('eldifi')], 'syl', 'd e. ( 1 ... M )')
    dnsq = fqd([ddif, w.inst('eldifn')], 'syl', '-. d e. %s' % SQM)
    nsq2 = fqd([fqd([elsqm], 'a1i',
                    '( d e. %s <-> ( d e. ( 1 ... M ) /\\ ( mmu ` d ) =/= 0 ) )' % SQM), dnsq],
               'mtbid', '-. ( d e. ( 1 ... M ) /\\ ( mmu ` d ) =/= 0 )')
    CJ = '( %s /\\ ( mmu ` d ) =/= 0 )' % CQD
    jcq = w.s([w.s([dfzq], 'adantr', '( %s -> d e. ( 1 ... M ) )' % CJ),
               w.s([], 'simpr', '( %s -> ( mmu ` d ) =/= 0 )' % CJ)], 'jca',
              '( %s -> ( d e. ( 1 ... M ) /\\ ( mmu ` d ) =/= 0 ) )' % CJ)
    mu0q = fqd([nsq2, jcq], 'mtand', '-. ( mmu ` d ) =/= 0')
    ifq = fqd([mu0q], 'iffalsed', '%s = 0' % SQ3('d'))
    dnnq = fqd([dfzq, w.inst('elfznn')], 'syl', 'd e. NN')
    vanq = fqd([fqd([ifq], 'oveq1d', '%s = ( 0 / d )' % TERM3('d')),
                fqd([fqd([dnnq], 'nncnd', 'd e. CC'), fqd([dnnq], 'nnne0d', 'd =/= 0')], 'div0d',
                    '( 0 / d ) = 0')], 'eqtrd', '%s = 0' % TERM3('d'))
    ssum = st([ssm, trmcq, vanq, finM], 'fsumss', '%s = %s' % (S1, S0))
    # the outer product over the primes up to M
    CP2 = '( %s /\\ p e. %s )' % (A, PF(NR))
    fp2 = mkst(w, CP2)
    pprm2 = fp2([fp2([], 'simpr', 'p e. %s' % PF(NR)), w.inst('elrabi')], 'syl', 'p e. Prime')
    cp2 = pclos3(w, fp2, 'p', pprm2)
    pxc2 = fp2([cp2['pc'], cp2['p1c']], 'mulcld', '( p x. ( p - 1 ) ) e. CC')
    pxne2 = fp2([cp2['pm1rp']], 'rpne0d', '( p x. ( p - 1 ) ) =/= 0')
    thc2 = fp2([w.s([], '3cn', '3 e. CC')], 'a1i', '3 e. CC')
    gex2 = fp2([fp2([thc2, pxc2, pxne2], 'divcld', '( 3 / ( p x. ( p - 1 ) ) ) e. CC'),
                w.inst('elex')], 'syl', '( 3 / ( p x. ( p - 1 ) ) ) e. _V')
    gv2 = fp2([pprm2, gex2, gv], 'syl2anc', '( %s ` p ) = ( 3 / ( p x. ( p - 1 ) ) )' % G4)
    pe1 = st([fp2([gv2], 'oveq2d',
             '( 1 + ( %s ` p ) ) = ( 1 + ( 3 / ( p x. ( p - 1 ) ) ) )' % G4)], 'prodeq2dv',
             '%s = prod_ p e. %s ( 1 + ( 3 / ( p x. ( p - 1 ) ) ) )' % (P1, PF(NR)))
    pe2 = st([nset2], 'prodeq1d',
             'prod_ p e. %s ( 1 + ( 3 / ( p x. ( p - 1 ) ) ) ) = %s' % (PF(NR), P2))
    pe3 = st([pe1, pe2], 'eqtrd', '%s = %s' % (P1, P2))
    thrp = st([w.s([], '3rp', '3 e. RR+')], 'a1i', '3 e. RR+')
    ppu = st([m, thrp, w.inst('primprodub')], 'syl2anc', '%s <_ ( exp ` 3 )' % P2)
    # assemble
    a1 = st([e1, key], 'eqtrd', '%s = %s' % (S2, P1))
    a2 = st([a1, pe3], 'eqtrd', '%s = %s' % (S2, P2))
    a3 = st([less, a2], 'breqtrd', '%s <_ %s' % (S1, P2))
    a4 = st([st([ssum], 'eqcomd', '%s = %s' % (S0, S1)), a3], 'eqbrtrd', '%s <_ %s' % (S0, P2))
    CM = '( %s /\\ d e. ( 1 ... M ) )' % A
    fm2 = mkst(w, CM)
    dnnm = fm2([fm2([], 'simpr', 'd e. ( 1 ... M )'), w.inst('elfznn')], 'syl', 'd e. NN')
    cm2 = sq3clos(w, fm2, 'd', dnnm)
    drpm = fm2([dnnm], 'nnrpd', 'd e. RR+')
    trmm = fm2([cm2['ifre'], drpm], 'rerpdivcld', '%s e. RR' % TERM3('d'))
    s0re = st([finM, trmm], 'fsumrecl', '%s e. RR' % S0)
    CPM = '( %s /\\ p e. %s )' % (A, PM)
    fpm = mkst(w, CPM)
    pprm3 = fpm([fpm([w.s([], 'inss2', '%s C_ Prime' % PM)], 'a1i', '%s C_ Prime' % PM),
                 fpm([], 'simpr', 'p e. %s' % PM)], 'sseldd', 'p e. Prime')
    cp3 = pclos3(w, fpm, 'p', pprm3)
    thr3 = fpm([w.s([], '3re', '3 e. RR')], 'a1i', '3 e. RR')
    pxr3 = fpm([thr3, cp3['pm1rp']], 'rerpdivcld', '( 3 / ( p x. ( p - 1 ) ) ) e. RR')
    one3 = fpm([], '1red', '1 e. RR')
    bd3 = fpm([one3, pxr3], 'readdcld', '( 1 + ( 3 / ( p x. ( p - 1 ) ) ) ) e. RR')
    p2re = st([finpm, bd3], 'fprodrecl', '%s e. RR' % P2)
    efre = st([st([w.s([], '3re', '3 e. RR')], 'a1i', '3 e. RR')], 'reefcld', '( exp ` 3 ) e. RR')
    w.qed([s0re, p2re, efre, a4, ppu], 'letrd', '( %s -> %s <_ ( exp ` 3 ) )' % (A, S0))
    return w


def tsqinner():
    w = W('tsqinner', 'The inner sum bound for the squared totient ratio estimate.')
    A = '( M e. NN /\\ D e. ( 1 ... M ) )'
    FZ = '( 1 ... ( |_ ` ( M / D ) ) )'
    LOG = '( 1 + ( log ` M ) )'
    SUM = 'sum_ m e. %s ( %s / ( D x. m ) )' % (FZ, SQ3('D'))
    HS = 'sum_ m e. %s ( 1 / m )' % FZ
    st = mkst(w, A)
    m = st([], 'simpl', 'M e. NN')
    dfz = st([], 'simpr', 'D e. ( 1 ... M )')
    d = st([dfz, w.inst('elfznn')], 'syl', 'D e. NN')
    dc = st([d], 'nncnd', 'D e. CC')
    dne = st([d], 'nnne0d', 'D =/= 0')
    drp = st([d], 'nnrpd', 'D e. RR+')
    cs = sq3clos(w, st, 'D', d)
    hh3 = w.s([cs['q0']], 'adantr',
              '( ( %s /\\ ( mmu ` D ) =/= 0 ) -> 0 <_ ( ( 3 ^ %s ) / ( phi ` D ) ) )'
              % (A, OM('D')))
    hh4 = w.s([st([cs['zre']], 'leidd', '0 <_ 0')], 'adantr',
              '( ( %s /\\ -. ( mmu ` D ) =/= 0 ) -> 0 <_ 0 )' % A)
    if0 = st([cs['b1'], cs['b2'], hh3, hh4], 'ifbothda', '0 <_ %s' % SQ3('D'))
    ifre = cs['ifre']
    ifc = st([ifre], 'recnd', '%s e. CC' % SQ3('D'))
    edr = st([ifre, drp], 'rerpdivcld', '( %s / D ) e. RR' % SQ3('D'))
    ed0 = st([ifre, drp, if0], 'divge0d', '0 <_ ( %s / D )' % SQ3('D'))
    edc = st([ifc, dc, dne], 'divcld', '( %s / D ) e. CC' % SQ3('D'))
    fin = st([], 'fzfid', '%s e. Fin' % FZ)
    harm = st([m, dfz, w.inst('harmub')], 'syl2anc', '%s <_ %s' % (HS, LOG))
    BM = '( %s /\\ m e. %s )' % (A, FZ)
    fm = mkst(w, BM)
    mnn = fm([fm([], 'simpr', 'm e. %s' % FZ), w.inst('elfznn')], 'syl', 'm e. NN')
    mc = fm([mnn], 'nncnd', 'm e. CC')
    mne = fm([mnn], 'nnne0d', 'm =/= 0')
    mrp = fm([mnn], 'nnrpd', 'm e. RR+')
    ifcm = fm([ifc], 'adantr', '%s e. CC' % SQ3('D'))
    dcm = fm([dc], 'adantr', 'D e. CC')
    dnem = fm([dne], 'adantr', 'D =/= 0')
    edcm = fm([edc], 'adantr', '( %s / D ) e. CC' % SQ3('D'))
    dd = fm([ifcm, dcm, dnem, mc, mne], 'divdiv1d',
            '( ( %s / D ) / m ) = ( %s / ( D x. m ) )' % (SQ3('D'), SQ3('D')))
    dr = fm([edcm, mc, mne], 'divrecd',
            '( ( %s / D ) / m ) = ( ( %s / D ) x. ( 1 / m ) )' % (SQ3('D'), SQ3('D')))
    teq = fm([dd, dr], 'eqtr3d',
             '( %s / ( D x. m ) ) = ( ( %s / D ) x. ( 1 / m ) )' % (SQ3('D'), SQ3('D')))
    recc = fm([fm([mrp], 'rpreccld', '( 1 / m ) e. RR+')], 'rpcnd', '( 1 / m ) e. CC')
    recr = fm([fm([mrp], 'rpreccld', '( 1 / m ) e. RR+')], 'rpred', '( 1 / m ) e. RR')
    e1 = st([teq], 'sumeq2dv',
            '%s = sum_ m e. %s ( ( %s / D ) x. ( 1 / m ) )' % (SUM, FZ, SQ3('D')))
    mul = st([fin, edc, recc], 'fsummulc2',
             '( ( %s / D ) x. %s ) = sum_ m e. %s ( ( %s / D ) x. ( 1 / m ) )'
             % (SQ3('D'), HS, FZ, SQ3('D')))
    e2 = st([e1, mul], 'eqtr4d', '%s = ( ( %s / D ) x. %s )' % (SUM, SQ3('D'), HS))
    hsre = st([fin, recr], 'fsumrecl', '%s e. RR' % HS)
    mrp2 = st([m], 'nnrpd', 'M e. RR+')
    logm = st([mrp2], 'relogcld', '( log ` M ) e. RR')
    one = st([], '1red', '1 e. RR')
    logr = st([one, logm], 'readdcld', '%s e. RR' % LOG)
    lem = st([hsre, logr, edr, ed0, harm], 'lemul2ad',
             '( ( %s / D ) x. %s ) <_ ( ( %s / D ) x. %s )' % (SQ3('D'), HS, SQ3('D'), LOG))
    w.qed([e2, lem], 'eqbrtrd',
          '( %s -> %s <_ ( ( %s / D ) x. %s ) )' % (A, SUM, SQ3('D'), LOG))
    return w


def totsumsq():
    w = W('totsumsq',
          'The sum of the square of m over its totient, divided by m, up to M, is at most '
          'e cubed x. ( 1 + log M ).')
    A = 'M e. NN'
    LOG = '( 1 + ( log ` M ) )'
    FY = '( 1 ... ( |_ ` M ) )'
    FZd = '( 1 ... ( |_ ` ( M / d ) ) )'
    DVN = '{ x e. NN | x || n }'
    IB = '( %s / n )' % SQ3('d')
    IC = '( %s / ( d x. m ) )' % SQ3('d')
    T0 = '( ( ( n / ( phi ` n ) ) ^ 2 ) / n )'
    TM = '( ( ( m / ( phi ` m ) ) ^ 2 ) / m )'
    S0 = 'sum_ n e. ( 1 ... M ) %s' % T0
    SM = 'sum_ m e. ( 1 ... M ) %s' % TM
    S1 = 'sum_ n e. ( 1 ... M ) sum_ d e. %s %s' % (DVN, IB)
    S1F = 'sum_ n e. %s sum_ d e. %s %s' % (FY, DVN, IB)
    S2F = 'sum_ d e. %s sum_ m e. %s %s' % (FY, FZd, IC)
    S2 = 'sum_ d e. ( 1 ... M ) sum_ m e. %s %s' % (FZd, IC)
    S3 = 'sum_ d e. ( 1 ... M ) ( ( %s / d ) x. %s )' % (SQ3('d'), LOG)
    SK = 'sum_ d e. ( 1 ... M ) ( %s / d )' % SQ3('d')
    st = mkst(w, A)
    m = w.s([], 'id', '( %s -> M e. NN )' % A)
    mz = st([m], 'nnzd', 'M e. ZZ')
    mr = st([m], 'nnred', 'M e. RR')
    mrp = st([m], 'nnrpd', 'M e. RR+')
    fl = st([mz, w.inst('flid')], 'syl', '( |_ ` M ) = M')
    fzeq = st([fl], 'oveq2d', '%s = ( 1 ... M )' % FY)
    fin = st([], 'fzfid', '( 1 ... M ) e. Fin')
    logm = st([mrp], 'relogcld', '( log ` M ) e. RR')
    one = st([], '1red', '1 e. RR')
    logr = st([one, logm], 'readdcld', '%s e. RR' % LOG)
    m1 = st([m, w.inst('nnge1')], 'syl', '1 <_ M')
    log0 = st([mr, m1, w.inst('logge0')], 'syl2anc', '0 <_ ( log ` M )')
    z1 = st([w.s([], '0le1', '0 <_ 1')], 'a1i', '0 <_ 1')
    logge = st([one, logm, z1, log0], 'addge0d', '0 <_ %s' % LOG)
    # ( 1 ) the termwise bound
    BN = '( %s /\\ n e. ( 1 ... M ) )' % A
    fn = mkst(w, BN)
    nnn = fn([fn([], 'simpr', 'n e. ( 1 ... M )'), w.inst('elfznn')], 'syl', 'n e. NN')
    nc = fn([nnn], 'nncnd', 'n e. CC')
    nne = fn([nnn], 'nnne0d', 'n =/= 0')
    nrp = fn([nnn], 'nnrpd', 'n e. RR+')
    nr = fn([nnn], 'nnred', 'n e. RR')
    phnn = fn([nnn, w.inst('phicl')], 'syl', '( phi ` n ) e. NN')
    phrp = fn([phnn], 'nnrpd', '( phi ` n ) e. RR+')
    qr = fn([nr, phrp], 'rerpdivcld', '( n / ( phi ` n ) ) e. RR')
    qsqr = fn([qr], 'resqcld', '( ( n / ( phi ` n ) ) ^ 2 ) e. RR')
    finn = fn([nnn, w.inst('dvdsfi')], 'syl', '%s e. Fin' % DVN)
    tsq = fn([nnn, w.inst('tsqkey')], 'syl',
             '( ( n / ( phi ` n ) ) ^ 2 ) <_ sum_ d e. %s %s' % (DVN, SQ3('d')))
    BND = '( %s /\\ d e. %s )' % (BN, DVN)
    fnd = mkst(w, BND)
    dnn = fnd([fnd([], 'simpr', 'd e. %s' % DVN), w.inst('elrabi')], 'syl', 'd e. NN')
    cd = sq3clos(w, fnd, 'd', dnn)
    ifcd = fnd([cd['ifre']], 'recnd', '%s e. CC' % SQ3('d'))
    sumre = fn([finn, cd['ifre']], 'fsumrecl', 'sum_ d e. %s %s e. RR' % (DVN, SQ3('d')))
    dvle = fn([qsqr, sumre, nrp, tsq], 'lediv1dd',
              '( ( ( n / ( phi ` n ) ) ^ 2 ) / n ) <_ ( sum_ d e. %s %s / n )' % (DVN, SQ3('d')))
    dvc = fn([finn, nc, ifcd, nne], 'fsumdivc',
             '( sum_ d e. %s %s / n ) = sum_ d e. %s %s' % (DVN, SQ3('d'), DVN, IB))
    term = fn([dvle, dvc], 'breqtrd', '%s <_ sum_ d e. %s %s' % (T0, DVN, IB))
    # closures for the sums
    nrpd = fnd([nrp], 'adantr', 'n e. RR+')
    ibred = fnd([cd['ifre'], nrpd], 'rerpdivcld', '%s e. RR' % IB)
    insre = fn([finn, ibred], 'fsumrecl', 'sum_ d e. %s %s e. RR' % (DVN, IB))
    t0re = fn([qsqr, nrp], 'rerpdivcld', '%s e. RR' % T0)
    sle1 = st([fin, t0re, insre, term], 'fsumle', '%s <_ %s' % (S0, S1))
    # ( 2 ) the double-sum swap
    sub = w.s([], 'oveq2', '( n = ( d x. m ) -> %s = %s )' % (IB, IC))
    BND2 = '( %s /\\ ( n e. %s /\\ d e. %s ) )' % (A, FY, DVN)
    fnd2 = mkst(w, BND2)
    pr = fnd2([], 'simpr', '( n e. %s /\\ d e. %s )' % (FY, DVN))
    nfz2 = fnd2([pr], 'simpld', 'n e. %s' % FY)
    dvs2 = fnd2([pr], 'simprd', 'd e. %s' % DVN)
    nnn2 = fnd2([nfz2, w.inst('elfznn')], 'syl', 'n e. NN')
    dnn2 = fnd2([dvs2, w.inst('elrabi')], 'syl', 'd e. NN')
    cd2 = sq3clos(w, fnd2, 'd', dnn2)
    nrp2 = fnd2([nnn2], 'nnrpd', 'n e. RR+')
    ibre2 = fnd2([cd2['ifre'], nrp2], 'rerpdivcld', '%s e. RR' % IB)
    ibc2 = fnd2([ibre2], 'recnd', '%s e. CC' % IB)
    swap = st([sub, mr, ibc2], 'dvdsflsumcom', '%s = %s' % (S1F, S2F))
    e2a = st([fzeq], 'sumeq1d', '%s = %s' % (S1F, S1))
    e2b = st([fzeq], 'sumeq1d', '%s = %s' % (S2F, S2))
    e2 = st([st([e2a], 'eqcomd', '%s = %s' % (S1, S1F)),
             st([swap, e2b], 'eqtrd', '%s = %s' % (S1F, S2))], 'eqtrd', '%s = %s' % (S1, S2))
    # ( 3 ) the inner bound
    BD = '( %s /\\ d e. ( 1 ... M ) )' % A
    fd = mkst(w, BD)
    dfz = fd([], 'simpr', 'd e. ( 1 ... M )')
    dnnd = fd([dfz, w.inst('elfznn')], 'syl', 'd e. NN')
    inner = fd([fd([m], 'adantr', 'M e. NN'), dfz, w.inst('tsqinner')], 'syl2anc',
               'sum_ m e. %s %s <_ ( ( %s / d ) x. %s )' % (FZd, IC, SQ3('d'), LOG))
    cD = sq3clos(w, fd, 'd', dnnd)
    drpD = fd([dnnd], 'nnrpd', 'd e. RR+')
    edrD = fd([cD['ifre'], drpD], 'rerpdivcld', '( %s / d ) e. RR' % SQ3('d'))
    edcD = fd([edrD], 'recnd', '( %s / d ) e. CC' % SQ3('d'))
    logrD = fd([logr], 'adantr', '%s e. RR' % LOG)
    prrD = fd([edrD, logrD], 'remulcld', '( ( %s / d ) x. %s ) e. RR' % (SQ3('d'), LOG))
    finD = fd([], 'fzfid', '%s e. Fin' % FZd)
    BDM = '( %s /\\ m e. %s )' % (BD, FZd)
    fdm = mkst(w, BDM)
    mnnD = fdm([fdm([], 'simpr', 'm e. %s' % FZd), w.inst('elfznn')], 'syl', 'm e. NN')
    dnnD2 = fdm([dnnd], 'adantr', 'd e. NN')
    dmD = fdm([dnnD2, mnnD], 'nnmulcld', '( d x. m ) e. NN')
    dmrpD = fdm([dmD], 'nnrpd', '( d x. m ) e. RR+')
    ifrDm = fdm([cD['ifre']], 'adantr', '%s e. RR' % SQ3('d'))
    icre = fdm([ifrDm, dmrpD], 'rerpdivcld', '%s e. RR' % IC)
    insre2 = fd([finD, icre], 'fsumrecl', 'sum_ m e. %s %s e. RR' % (FZd, IC))
    sle = st([fin, insre2, prrD, inner], 'fsumle', '%s <_ %s' % (S2, S3))
    # ( 4 ) factor out and apply tsqconst
    logc = st([logr], 'recnd', '%s e. CC' % LOG)
    mulc = st([fin, logc, edcD], 'fsummulc1', '( %s x. %s ) = %s' % (SK, LOG, S3))
    skre = st([fin, edrD], 'fsumrecl', '%s e. RR' % SK)
    tsc = st([], 'tsqconst', '%s <_ ( exp ` 3 )' % SK)
    efre = st([st([w.s([], '3re', '3 e. RR')], 'a1i', '3 e. RR')], 'reefcld', '( exp ` 3 ) e. RR')
    lem = st([skre, efre, logr, logge, tsc], 'lemul1ad',
             '( %s x. %s ) <_ ( ( exp ` 3 ) x. %s )' % (SK, LOG, LOG))
    le3 = st([st([mulc], 'eqcomd', '%s = ( %s x. %s )' % (S3, SK, LOG)), lem], 'eqbrtrd',
             '%s <_ ( ( exp ` 3 ) x. %s )' % (S3, LOG))
    s0re = st([fin, t0re], 'fsumrecl', '%s e. RR' % S0)
    s1re = st([fin, insre], 'fsumrecl', '%s e. RR' % S1)
    s2re = st([fin, insre2], 'fsumrecl', '%s e. RR' % S2)
    s3re = st([fin, prrD], 'fsumrecl', '%s e. RR' % S3)
    efl = st([efre, logr], 'remulcld', '( ( exp ` 3 ) x. %s ) e. RR' % LOG)
    t1 = st([s2re, s3re, efl, sle, le3], 'letrd', '%s <_ ( ( exp ` 3 ) x. %s )' % (S2, LOG))
    t2 = st([e2, t1], 'eqbrtrd', '%s <_ ( ( exp ` 3 ) x. %s )' % (S1, LOG))
    t3 = st([s0re, s1re, efl, sle1, t2], 'letrd', '%s <_ ( ( exp ` 3 ) x. %s )' % (S0, LOG))
    cba = w.s([], 'fveq2', '( n = m -> ( phi ` n ) = ( phi ` m ) )')
    cbb = w.s([w.s([], 'id', '( n = m -> n = m )'), cba], 'oveq12d',
              '( n = m -> ( n / ( phi ` n ) ) = ( m / ( phi ` m ) ) )')
    cbc = w.s([cbb], 'oveq1d',
              '( n = m -> ( ( n / ( phi ` n ) ) ^ 2 ) = ( ( m / ( phi ` m ) ) ^ 2 ) )')
    cbd = w.s([cbc, w.s([], 'id', '( n = m -> n = m )')], 'oveq12d',
              '( n = m -> %s = %s )' % (T0, TM))
    cbs = st([w.s([cbd], 'cbvsumv', '%s = %s' % (S0, SM))], 'a1i', '%s = %s' % (S0, SM))
    w.qed([st([cbs], 'eqcomd', '%s = %s' % (SM, S0)), t3], 'eqbrtrd',
          '( %s -> %s <_ ( ( exp ` 3 ) x. %s ) )' % (A, SM, LOG))
    return w


if __name__ == '__main__':
    import sys
    for f in sys.argv[1:] or ['tsqfac']:
        globals()[f]().run()
