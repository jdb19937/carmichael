"""Sortie GF1, section E: the Dirichlet polynomial M_h (gf1hbv0, gf1hbvs, gf1mhh, gf1mhb, gf1hm).
MM_DB=sorties/gf1.mm MM_ENGINE=mmatch python3 tools/gen/gf1_e.py [LABEL...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from gf1lib import *

only = sys.argv[1:]
S['gf1hbv0'] = '( ( ( ( R e. NN /\\ T e. NN ) /\\ D e. NN ) /\\ -. D || ( R x. T ) ) -> ( ( R hBV T ) ` D ) = 0 )'
FM = '( ( mmu ` %s ) x. ( phi ` %s ) )'
FAC = lambda p: '( ( if ( %s || R , %s , 1 ) x. if ( %s || T , %s , 1 ) ) - 1 )' % (p, FM % (p, p), p, FM % (p, p))
PSET = '{ q e. Prime | q || D }'
PROD = 'prod_ p e. %s %s' % (PSET, FAC('p'))


def gen_hbv0():
    w = W('gf1hbv0', '` h ( d ; r , r\' ) = 0 ` unless ` d || r r\' ` (Lean ` hBV_eq_zero_of_not_dvd ` ; ~ z5sqfpdvd ).')
    X0, CONC = split_imp(S['gf1hbv0'])
    d = mk(w, X0)
    rn = proj(w, X0, 'R e. NN'); tn = proj(w, X0, 'T e. NN'); dn = proj(w, X0, 'D e. NN'); nd = proj(w, X0, '-. D || ( R x. T )')
    HB = '( ( R hBV T ) ` D )'
    hv = d('syl', [d('jca', [d('jca', [rn, tn], '( R e. NN /\\ T e. NN )'), dn], '( ( R e. NN /\\ T e. NN ) /\\ D e. NN )'), w.inst('z5hbvval')],
           '%s = if ( ( mmu ` D ) =/= 0 , %s , 0 )' % (HB, PROD))
    PSI = '( mmu ` D ) =/= 0'
    # branch -. psi
    Xa = '( %s /\\ -. %s )' % (X0, PSI)
    ba = D(w, Xa, 'eqtrd', [lift(w, hv, Xa), D(w, Xa, 'iffalsed', [w.s([], 'simpr', '( %s -> -. %s )' % (Xa, PSI))], 'if ( %s , %s , 0 ) = 0' % (PSI, PROD))], '%s = 0' % HB)
    # branch psi
    Xb = '( %s /\\ %s )' % (X0, PSI)
    db = mk(w, Xb); Lb = lambda st: lift(w, st, Xb)
    it = db('iftrued', [w.s([], 'simpr', '( %s -> %s )' % (Xb, PSI))], 'if ( %s , %s , 0 ) = %s' % (PSI, PROD, PROD))
    RT = '( R x. T )'
    rtn = db('nnmulcld', [Lb(rn), Lb(tn)], '%s e. NN' % RT)
    ALL = 'A. p e. Prime ( p || D -> p || %s )' % RT
    Xc = '( %s /\\ %s )' % (Xb, ALL)
    dv = D(w, Xc, 'syl', [D(w, Xc, 'jca', [D(w, Xc, 'jca', [lift(w, Lb(dn), Xc), lift(w, w.s([], 'simpr', '( %s -> %s )' % (Xb, PSI)), Xc)], '( D e. NN /\\ %s )' % PSI),
                                           D(w, Xc, 'jca', [lift(w, rtn, Xc), w.s([], 'simpr', '( %s -> %s )' % (Xc, ALL))], '( %s e. NN /\\ %s )' % (RT, ALL))],
                                  '( ( D e. NN /\\ %s ) /\\ ( %s e. NN /\\ %s ) )' % (PSI, RT, ALL)), w.inst('z5sqfpdvd')], 'D || %s' % RT)
    ex = w.s([dv], 'ex', '( %s -> ( %s -> D || %s ) )' % (Xb, ALL, RT))
    nall = db('mtod', [Lb(nd), ex], '-. %s' % ALL)
    EX_ = 'E. m e. Prime -. ( m || D -> m || %s )' % RT
    rn_ = w.s([], 'rexnal', '( E. p e. Prime -. ( p || D -> p || %s ) <-> -. %s )' % (RT, ALL))
    cb = w.s([w.s([w.s([w.s([], 'breq1', '( p = m -> ( p || D <-> m || D ) )'), w.s([], 'breq1', '( p = m -> ( p || %s <-> m || %s ) )' % (RT, RT))], 'imbi12d',
                        '( p = m -> ( ( p || D -> p || %s ) <-> ( m || D -> m || %s ) ) )' % (RT, RT))], 'notbid', '( p = m -> ( -. ( p || D -> p || %s ) <-> -. ( m || D -> m || %s ) ) )' % (RT, RT))],
             'cbvrexvw', '( E. p e. Prime -. ( p || D -> p || %s ) <-> %s )' % (RT, EX_))
    exs = db('mpbird', [nall, a1(w, Xb, 'bitr3i', '( %s <-> -. %s )' % (EX_, ALL), [cb, rn_])], EX_)
    # witness m
    Xm = '( ( %s /\\ m e. Prime ) /\\ -. ( m || D -> m || %s ) )' % (Xb, RT)
    dm = mk(w, Xm); Lm = lambda st: lift(w, st, Xm)
    an = dm('mpbir' if False else 'syl', [w.s([], 'simpr', '( %s -> -. ( m || D -> m || %s ) )' % (Xm, RT)), w.s([w.s([], 'annim', '( ( m || D /\\ -. m || %s ) <-> -. ( m || D -> m || %s ) )' % (RT, RT))], 'biimpri',
                                                                                            '( -. ( m || D -> m || %s ) -> ( m || D /\\ -. m || %s ) )' % (RT, RT))],
            '( m || D /\\ -. m || %s )' % RT)
    mD = dm('simpld', [an], 'm || D'); mRT = dm('simprd', [an], '-. m || %s' % RT)
    mp = proj(w, Xm, 'm e. Prime')
    mz = dm('nnzd', [dm('syl', [mp, w.inst('prmnn')], 'm e. NN')], 'm e. ZZ')
    rz = dm('nnzd', [Lm(Lb(rn)) if False else lift(w, rn, Xm)], 'R e. ZZ'); tz = dm('nnzd', [lift(w, tn, Xm)], 'T e. ZZ')
    nR = dm('mtod', [mRT, dm('syl3anc', [mz, rz, tz, w.inst('dvdsmultr1')], '( m || R -> m || %s )' % RT)], '-. m || R')
    nT = dm('mtod', [mRT, dm('syl3anc', [mz, rz, tz, w.inst('dvdsmultr2')], '( m || T -> m || %s )' % RT)], '-. m || T')
    mset = dm('mpbird', [dm('jca', [mp, mD], '( m e. Prime /\\ m || D )'),
                         a1(w, Xm, 'elrab', '( m e. %s <-> ( m e. Prime /\\ m || D ) )' % PSET, [w.s([], 'breq1', '( q = m -> ( q || D <-> m || D ) )')])], 'm e. %s' % PSET)
    Xpm = '( %s /\\ p = m )' % Xm
    dpm = mk(w, Xpm)
    pm = w.s([], 'simpr', '( %s -> p = m )' % Xpm)
    npR = dpm('mtbird', [lift(w, nR, Xpm), dpm('breq1d', [pm], '( p || R <-> m || R )')], '-. p || R')
    npT = dpm('mtbird', [lift(w, nT, Xpm), dpm('breq1d', [pm], '( p || T <-> m || T )')], '-. p || T')
    i1 = dpm('iffalsed', [npR], 'if ( p || R , %s , 1 ) = 1' % (FM % ('p', 'p')))
    i2 = dpm('iffalsed', [npT], 'if ( p || T , %s , 1 ) = 1' % (FM % ('p', 'p')))
    f0 = dpm('oveq1d', [dpm('oveq12d', [i1, i2], '( if ( p || R , %s , 1 ) x. if ( p || T , %s , 1 ) ) = ( 1 x. 1 )' % (FM % ('p', 'p'), FM % ('p', 'p')))],
             '%s = ( ( 1 x. 1 ) - 1 )' % FAC('p'))
    f1 = dpm('eqtrd', [f0, a1(w, Xpm, 'eqtri', '( ( 1 x. 1 ) - 1 ) = 0', [w.s([w.s([], '1t1e1', '( 1 x. 1 ) = 1')], 'oveq1i', '( ( 1 x. 1 ) - 1 ) = ( 1 - 1 )'), w.s([], '1m1e0', '( 1 - 1 ) = 0')])],
             '%s = 0' % FAC('p'))
    Xps = '( %s /\\ p e. %s )' % (Xm, PSET)
    dps = mk(w, Xps)
    ppr = dps('simpld', [dps('mpbid', [w.s([], 'simpr', '( %s -> p e. %s )' % (Xps, PSET)), a1(w, Xps, 'elrab', '( p e. %s <-> ( p e. Prime /\\ p || D ) )' % PSET, [w.s([], 'breq1', '( q = p -> ( q || D <-> p || D ) )')])],
                                '( p e. Prime /\\ p || D )')], 'p e. Prime')
    pnn = dps('syl', [ppr, w.inst('prmnn')], 'p e. NN')
    fmc = dps('mulcld', [dps('zcnd', [dps('syl', [pnn, w.inst('mucl')], '( mmu ` p ) e. ZZ')], '( mmu ` p ) e. CC'), dps('nncnd', [dps('syl', [pnn, w.inst('phicl')], '( phi ` p ) e. NN')], '( phi ` p ) e. CC')],
                  '%s e. CC' % (FM % ('p', 'p')))
    one = a1(w, Xps, 'ax-1cn', '1 e. CC')
    fc = dps('subcld', [dps('mulcld', [dps('ifcld', [fmc, one], 'if ( p || R , %s , 1 ) e. CC' % (FM % ('p', 'p'))), dps('ifcld', [fmc, one], 'if ( p || T , %s , 1 ) e. CC' % (FM % ('p', 'p')))],
                                   '( if ( p || R , %s , 1 ) x. if ( p || T , %s , 1 ) ) e. CC' % (FM % ('p', 'p'), FM % ('p', 'p'))), one], '%s e. CC' % FAC('p'))
    pfin = dm('syl', [lift(w, dn, Xm), w.inst('prmdvdsfi')], '%s e. Fin' % PSET)
    p0 = dm('fprodeq0g', [w.s([], 'nfv', 'F/ p %s' % Xm), pfin, fc, mset, f1], '%s = 0' % PROD)
    rl = w.s([w.s([p0], 'ex', '( ( %s /\\ m e. Prime ) -> ( -. ( m || D -> m || %s ) -> %s = 0 ) )' % (Xb, RT, PROD))], 'rexlimdva', '( %s -> ( %s -> %s = 0 ) )' % (Xb, EX_, PROD))
    pz = db('mpd', [exs, rl], '%s = 0' % PROD)
    bb = chain(w, Xb, [HB, 'if ( %s , %s , 0 )' % (PSI, PROD), PROD, '0'], [Lb(hv), it, pz])
    fin = d('pm2.61dan', [bb, ba], CONC)
    w.qed([fin], 'idi', S['gf1hbv0'])
    return run(w, only)


def gen_hbvs():
    w = W('gf1hbvs', 'A divisor sum of ` h ( d ; r , r\' ) G ( d ) ` over ` d || K ` is the sum over the divisors of ` r r\' ` that divide ` K ` (Lean ` sum_divisors_hBV_eq ` ; ~ gf1hbv0 , ~ sumss ).')
    h1, h2 = ehyps(w, 'gf1hbvs')
    A = 'ph'
    d = mk(w, A)
    rn = d('simp1d', [h1], 'R e. NN'); tn = d('simp2d', [h1], 'T e. NN'); kn = d('simp3d', [h1], 'K e. NN')
    RT = '( R x. T )'
    DK = DIV('K'); DR = DIV(RT)
    E = '{ x e. NN | ( x || K /\\ x || %s ) }' % RT
    F = '( ( ( R hBV T ) ` d ) x. G )'
    IF = 'if ( d || K , %s , 0 )' % F
    def mem(S_, cond_x, cond_d, ctx, st):
        """( ctx -> ( d e. NN /\\ cond_d ) ) from st ( ctx -> d e. S_ )"""
        e = w.s([w.s([], 'breq1', '( x = d -> ( x || K <-> d || K ) )') if 'K' in cond_x and '/\\' not in cond_x else None] if False else [], 'idi', '') if False else None
        return None
    # membership lemmas as closed facts
    eK = w.s([w.s([], 'breq1', '( x = d -> ( x || K <-> d || K ) )')], 'elrab', '( d e. %s <-> ( d e. NN /\\ d || K ) )' % DK)
    eR = w.s([w.s([], 'breq1', '( x = d -> ( x || %s <-> d || %s ) )' % (RT, RT))], 'elrab', '( d e. %s <-> ( d e. NN /\\ d || %s ) )' % (DR, RT))
    eE = w.s([w.s([w.s([], 'breq1', '( x = d -> ( x || K <-> d || K ) )'), w.s([], 'breq1', '( x = d -> ( x || %s <-> d || %s ) )' % (RT, RT))], 'anbi12d',
                  '( x = d -> ( ( x || K /\\ x || %s ) <-> ( d || K /\\ d || %s ) ) )' % (RT, RT))], 'elrab', '( d e. %s <-> ( d e. NN /\\ ( d || K /\\ d || %s ) ) )' % (E, RT))
    # F e. CC on NN
    An = '( ph /\\ d e. NN )'
    dnn = w.s([], 'simpr', '( %s -> d e. NN )' % An)
    hre = D(w, An, 'syl', [D(w, An, 'jca', [D(w, An, 'jca', [lift(w, rn, An), lift(w, tn, An)], '( R e. NN /\\ T e. NN )'), dnn], '( ( R e. NN /\\ T e. NN ) /\\ d e. NN )'), w.inst('z5hbvre')],
           '( ( R hBV T ) ` d ) e. RR')
    fc = D(w, An, 'mulcld', [D(w, An, 'recnd', [hre], '( ( R hBV T ) ` d ) e. CC'), h2], '%s e. CC' % F)
    def from_set(Sset, eq, part):
        """( ( ph /\\ d e. Sset ) -> part ) where part is d e. NN or a divisibility conjunct"""
        Ad = '( ph /\\ d e. %s )' % Sset
        m = D(w, Ad, 'mpbid', [w.s([], 'simpr', '( %s -> d e. %s )' % (Ad, Sset)), a1(w, Ad, 'idi' if False else 'a1i' if False else 'mpbi' if False else 'eqid', '') if False else w.s([eq], 'a1i', '( %s -> %s )' % (Ad, w.lines[-1].split(' |- ', 1)[1]) ) if False else None], '') if False else None
        return None
    def ctx_mem(Sset, eq, rhs):
        Ad = '( ph /\\ d e. %s )' % Sset
        return Ad, D(w, Ad, 'mpbi' if False else 'sylib', [w.s([], 'simpr', '( %s -> d e. %s )' % (Ad, Sset)), eq], rhs)
    AE, mE = ctx_mem(E, eE, '( d e. NN /\\ ( d || K /\\ d || %s ) )' % RT)
    dE_nn = D(w, AE, 'simpld', [mE], 'd e. NN')
    fcE = D(w, AE, 'syl2anc' if False else 'mpd', [dE_nn, D(w, AE, 'ex' if False else 'idi', [], '') if False else w.s([w.s([fc], 'ex', '( ph -> ( d e. NN -> %s e. CC ) )' % F)], 'adantr', '( %s -> ( d e. NN -> %s e. CC ) )' % (AE, F))], '%s e. CC' % F)
    # E C_ DK and E C_ DR
    sub1 = d('ss2rabdv' if False else 'ss2rabdv', [w.s([w.s([], 'simpl', '( ( x || K /\\ x || %s ) -> x || K )' % RT)], 'a1d', '( ( ph /\\ x e. NN ) -> ( ( x || K /\\ x || %s ) -> x || K ) )' % RT) if False else
                                       D(w, '( ph /\\ x e. NN )', 'idi', [], '') if False else a1(w, '( ph /\\ x e. NN )', 'simpl', '( ( x || K /\\ x || %s ) -> x || K )' % RT)], '%s C_ %s' % (E, DK))
    sub2 = d('ss2rabdv', [a1(w, '( ph /\\ x e. NN )', 'simpr', '( ( x || K /\\ x || %s ) -> x || %s )' % (RT, RT))], '%s C_ %s' % (E, DR))
    uz = lambda S_: w.s([w.s([], 'ssrab2', '%s C_ NN' % S_), w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'sseqtri', '%s C_ ( ZZ>= ` 1 )' % S_)
    # LHS: on DK \ E, F = 0
    Adk = '( ph /\\ d e. ( %s \\ %s ) )' % (DK, E)
    dk = mk(w, Adk)
    ed = dk('eldifd' if False else 'sylib', [w.s([], 'simpr', '( %s -> d e. ( %s \\ %s ) )' % (Adk, DK, E)), w.s([], 'eldif', '( d e. ( %s \\ %s ) <-> ( d e. %s /\\ -. d e. %s ) )' % (DK, E, DK, E))],
             '( d e. %s /\\ -. d e. %s )' % (DK, E))
    inK = dk('sylib', [dk('simpld', [ed], 'd e. %s' % DK), eK], '( d e. NN /\\ d || K )')
    nE = dk('simprd', [ed], '-. d e. %s' % E)
    dnnk = dk('simpld', [inK], 'd e. NN'); dK = dk('simprd', [inK], 'd || K')
    # -. d || RT: else d e. E
    nRT = dk('mtod', [nE, w.s([dk('3jca' if False else 'jca', [dnnk, dK], '( d e. NN /\\ d || K )') if False else None] if False else [], 'idi', '') if False else
                      w.s([w.s([D(w, '( %s /\\ d || %s )' % (Adk, RT), 'mpbird', [D(w, '( %s /\\ d || %s )' % (Adk, RT), 'jca', [lift(w, dnnk, '( %s /\\ d || %s )' % (Adk, RT)),
                                                                                                                          D(w, '( %s /\\ d || %s )' % (Adk, RT), 'jca', [lift(w, dK, '( %s /\\ d || %s )' % (Adk, RT)), w.s([], 'simpr', '( ( %s /\\ d || %s ) -> d || %s )' % (Adk, RT, RT))],
                                                                                                                            '( d || K /\\ d || %s )' % RT)], '( d e. NN /\\ ( d || K /\\ d || %s ) )' % RT),
                                                                                  w.s([eE], 'a1i', '( ( %s /\\ d || %s ) -> ( d e. %s <-> ( d e. NN /\\ ( d || K /\\ d || %s ) ) ) )' % (Adk, RT, E, RT))], 'd e. %s' % E)], 'ex',
                              '( %s -> ( d || %s -> d e. %s ) )' % (Adk, RT, E))], 'idi', '( %s -> ( d || %s -> d e. %s ) )' % (Adk, RT, E))], '-. d || %s' % RT)
    h0 = dk('syl', [dk('jca', [dk('jca', [dk('jca', [lift(w, rn, Adk), lift(w, tn, Adk)], '( R e. NN /\\ T e. NN )'), dnnk], '( ( R e. NN /\\ T e. NN ) /\\ d e. NN )'), nRT],
                       '( ( ( R e. NN /\\ T e. NN ) /\\ d e. NN ) /\\ -. d || %s )' % RT), w.inst('gf1hbv0')], '( ( R hBV T ) ` d ) = 0')
    gck = dk('mpd', [dnnk, w.s([w.s([h2], 'ex', '( ph -> ( d e. NN -> G e. CC ) )')], 'adantr', '( %s -> ( d e. NN -> G e. CC ) )' % Adk)], 'G e. CC')
    f0 = dk('eqtrd', [dk('oveq1d', [h0], '%s = ( 0 x. G )' % F), dk('mul02d', [gck], '( 0 x. G ) = 0')], '%s = 0' % F)
    L1 = d('sumss', [sub1, fcE, f0, a1(w, A, 'sseqtri', '%s C_ ( ZZ>= ` 1 )' % DK, [w.s([], 'ssrab2', '%s C_ NN' % DK), w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')])],
           'sum_ d e. %s %s = sum_ d e. %s %s' % (E, F, DK, F))
    # RHS: on DR \ E, IF = 0
    Adr = '( ph /\\ d e. ( %s \\ %s ) )' % (DR, E)
    dr = mk(w, Adr)
    edr = dr('sylib', [w.s([], 'simpr', '( %s -> d e. ( %s \\ %s ) )' % (Adr, DR, E)), w.s([], 'eldif', '( d e. ( %s \\ %s ) <-> ( d e. %s /\\ -. d e. %s ) )' % (DR, E, DR, E))],
              '( d e. %s /\\ -. d e. %s )' % (DR, E))
    inR = dr('sylib', [dr('simpld', [edr], 'd e. %s' % DR), eR], '( d e. NN /\\ d || %s )' % RT)
    nE2 = dr('simprd', [edr], '-. d e. %s' % E)
    dnnr = dr('simpld', [inR], 'd e. NN'); dRT = dr('simprd', [inR], 'd || %s' % RT)
    Ak = '( %s /\\ d || K )' % Adr
    nK = dr('mtod', [nE2, w.s([D(w, Ak, 'mpbird', [D(w, Ak, 'jca', [lift(w, dnnr, Ak), D(w, Ak, 'jca', [w.s([], 'simpr', '( %s -> d || K )' % Ak), lift(w, dRT, Ak)], '( d || K /\\ d || %s )' % RT)],
                                                    '( d e. NN /\\ ( d || K /\\ d || %s ) )' % RT), w.s([eE], 'a1i', '( %s -> ( d e. %s <-> ( d e. NN /\\ ( d || K /\\ d || %s ) ) ) )' % (Ak, E, RT))], 'd e. %s' % E)],
                             'ex', '( %s -> ( d || K -> d e. %s ) )' % (Adr, E))], '-. d || K')
    if0 = dr('iffalsed', [nK], '%s = 0' % IF)
    ifE = D(w, AE, 'ifcld', [fcE, a1(w, AE, '0cn', '0 e. CC')], '%s e. CC' % IF)
    R1 = d('sumss', [sub2, ifE, if0, a1(w, A, 'sseqtri', '%s C_ ( ZZ>= ` 1 )' % DR, [w.s([], 'ssrab2', '%s C_ NN' % DR), w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')])],
           'sum_ d e. %s %s = sum_ d e. %s %s' % (E, IF, DR, IF))
    dKE = D(w, AE, 'simpld', [D(w, AE, 'simprd', [mE], '( d || K /\\ d || %s )' % RT)], 'd || K')
    se = d('sumeq2dv', [D(w, AE, 'iftrued', [dKE], '%s = %s' % (IF, F))], 'sum_ d e. %s %s = sum_ d e. %s %s' % (E, IF, E, F))
    fin = chain(w, A, ['sum_ d e. %s %s' % (DK, F), 'sum_ d e. %s %s' % (E, F), 'sum_ d e. %s %s' % (E, IF), 'sum_ d e. %s %s' % (DR, IF)], [('r', L1), ('r', se), R1])
    w.qed([fin], 'idi', S['gf1hbvs'])
    return run(w, only)


def mh_ctx(w, X0, nv, rv_, cf):
    """contexts and closure facts for the M_h sums: returns dict with steps under X1 = ( X0 /\\ r e. RS ), X2, X3"""
    RSs = RS('N', 'R')
    X1 = '( %s /\\ r e. %s )' % (X0, RSs)
    X2 = '( %s /\\ t e. %s )' % (X1, RSs)
    DV = DIV('( r x. t )')
    X3 = '( %s /\\ d e. %s )' % (X2, DV)
    rs = D(w, X0, 'syl', [D(w, X0, 'jca', [nv, rv_], '( N e. V /\\ R e. W )'), w.inst('z5rsetfi')], '( %s C_ ( 1 ... ( |_ ` R ) ) /\\ %s e. Fin )' % (RSs, RSs))
    rsf = D(w, X0, 'simprd', [rs], '%s e. Fin' % RSs)
    rss = D(w, X0, 'simpld', [rs], '%s C_ ( 1 ... ( |_ ` R ) )' % RSs)
    def nnof(X, v):
        m = D(w, X, 'sseldd', [lift(w, rss, X), w.s([], 'simpr', '( %s -> %s e. %s )' % (X, v, RSs)) if X.endswith('%s e. %s )' % (v, RSs)) else lift(w, w.s([], 'simpr', '( %s -> %s e. %s )' % (X1 if v == 'r' else X2, v, RSs)), X)],
              '%s e. ( 1 ... ( |_ ` R ) )' % v)
        return D(w, X, 'elfznnd' if False else 'syl', [m, w.inst('elfznn')], '%s e. NN' % v)
    r1 = nnof(X1, 'r')
    r2 = lift(w, r1, X2)
    t2 = nnof(X2, 't')
    rt2 = D(w, X2, 'nnmulcld', [r2, t2], '( r x. t ) e. NN')
    dvf = D(w, X2, 'syl', [rt2, w.inst('dvdsfi')], '%s e. Fin' % DV)
    d3in = w.s([], 'simpr', '( %s -> d e. %s )' % (X3, DV))
    d3 = D(w, X3, 'simpld', [D(w, X3, 'sylib', [d3in, w.s([w.s([], 'breq1', '( x = d -> ( x || ( r x. t ) <-> d || ( r x. t ) ) )')], 'elrab', '( d e. %s <-> ( d e. NN /\\ d || ( r x. t ) ) )' % DV)],
                                '( d e. NN /\\ d || ( r x. t ) )')], 'd e. NN')
    hr = D(w, X3, 'syl', [D(w, X3, 'jca', [D(w, X3, 'jca', [lift(w, r1, X3), lift(w, t2, X3)], '( r e. NN /\\ t e. NN )'), d3], '( ( r e. NN /\\ t e. NN ) /\\ d e. NN )'), w.inst('z5hbvre')],
           '( ( r hBV t ) ` d ) e. RR')
    cd = D(w, X3, 'ffvelcdmd', [lift(w, cf, X3), d3], '( C ` d ) e. CC')
    return dict(X1=X1, X2=X2, X3=X3, rsf=rsf, r1=r1, t2=t2, rt2=rt2, dvf=dvf, d3=d3, hr=hr, cd=cd, DV=DV, RSs=RSs)


INNER = lambda S_: '( ( ( ( r hBV t ) ` d ) x. ( C ` d ) ) x. ( d ^c -u %s ) )' % S_


def gen_mhh():
    w = W('gf1mhh', 'The Dirichlet polynomial ` M_h ( s , chi ) ` is entire (Lean ` differentiable_Mh ` ; ~ z6ehfs , ~ z6ehx ).')
    X0, CONC = split_imp(S['gf1mhh'])
    d = mk(w, X0)
    nv = proj(w, X0, 'N e. V'); rv_ = proj(w, X0, 'R e. W'); cf = proj(w, X0, 'C : NN --> CC')
    c = mh_ctx(w, X0, nv, rv_, cf)
    X1, X2, X3 = c['X1'], c['X2'], c['X3']
    hc = D(w, X3, 'mulcld', [D(w, X3, 'recnd', [c['hr']], '( ( r hBV t ) ` d ) e. CC'), c['cd']], '( ( ( r hBV t ) ` d ) x. ( C ` d ) ) e. CC')
    h1 = D(w, X3, 'z6ehc', [hc], HOL('( s e. CC |-> ( ( ( r hBV t ) ` d ) x. ( C ` d ) ) )', 'CC'))
    h2 = D(w, X3, 'syl', [D(w, X3, 'nnrpd', [c['d3']], 'd e. RR+'), w.inst('z6ehx')], HOL('( s e. CC |-> ( d ^c -u s ) )', 'CC'))
    h3 = D(w, X3, 'z6ehmul', [h1, h2], HOL('( s e. CC |-> %s )' % INNER('s'), 'CC'))
    SD = 'sum_ d e. %s %s' % (c['DV'], INNER('s'))
    h4 = D(w, X2, 'z6ehfs', [c['dvf'], h3], HOL('( s e. CC |-> %s )' % SD, 'CC'))
    rtc = D(w, X2, 'nncnd', [c['rt2']], '( r x. t ) e. CC')
    ic = D(w, X2, 'reccld', [rtc, D(w, X2, 'nnne0d', [c['rt2']], '( r x. t ) =/= 0')], '( 1 / ( r x. t ) ) e. CC')
    h5 = D(w, X2, 'z6ehmul', [D(w, X2, 'z6ehc', [ic], HOL('( s e. CC |-> ( 1 / ( r x. t ) ) )', 'CC')), h4], HOL('( s e. CC |-> ( ( 1 / ( r x. t ) ) x. %s ) )' % SD, 'CC'))
    ST = 'sum_ t e. %s ( ( 1 / ( r x. t ) ) x. %s )' % (c['RSs'], SD)
    h6 = D(w, X1, 'z6ehfs', [lift(w, c['rsf'], X1), h5], HOL('( s e. CC |-> %s )' % ST, 'CC'))
    h7 = d('z6ehfs', [c['rsf'], h6], HOL('( s e. CC |-> sum_ r e. %s %s )' % (c['RSs'], ST), 'CC'))
    w.qed([h7], 'idi', S['gf1mhh'])
    return run(w, only)


def gen_mhb():
    w = W('gf1mhb', '` abs M_h ( S , chi ) <_ Hmass ` on ` 0 <_ Re S ` for ` abs chi <_ 1 ` (Lean ` norm_Mh_le ` ; ~ fsumabs , ~ gf1cxb ).')
    X0, CONC = split_imp(S['gf1mhb'])
    d = mk(w, X0)
    nv = proj(w, X0, 'N e. V'); rv_ = proj(w, X0, 'R e. W'); cf = proj(w, X0, 'C : NN --> CC')
    call = proj(w, X0, 'A. k e. NN ( abs ` ( C ` k ) ) <_ 1')
    sc = proj(w, X0, 'S e. CC'); s0 = proj(w, X0, '0 <_ ( Re ` S )')
    c = mh_ctx(w, X0, nv, rv_, cf)
    X1, X2, X3 = c['X1'], c['X2'], c['X3']
    L3 = lambda st: lift(w, st, X3)
    x = INNER('S')
    HB = '( ( r hBV t ) ` d )'
    hc = D(w, X3, 'recnd', [c['hr']], '%s e. CC' % HB)
    cx = D(w, X3, 'syl', [D(w, X3, 'jca', [c['d3'], D(w, X3, 'jca', [L3(sc), L3(s0)], '( S e. CC /\\ 0 <_ ( Re ` S ) )')], '( d e. NN /\\ ( S e. CC /\\ 0 <_ ( Re ` S ) ) )'), w.inst('gf1cxb')],
           '( ( d ^c -u S ) e. CC /\\ ( abs ` ( d ^c -u S ) ) <_ 1 )')
    dsc = D(w, X3, 'simpld', [cx], '( d ^c -u S ) e. CC'); ds1 = D(w, X3, 'simprd', [cx], '( abs ` ( d ^c -u S ) ) <_ 1')
    hcd = D(w, X3, 'mulcld', [hc, c['cd']], '( %s x. ( C ` d ) ) e. CC' % HB)
    xc = D(w, X3, 'mulcld', [hcd, dsc], '%s e. CC' % x)
    cd1 = D(w, X3, 'mpd', [c['d3'], D(w, X3, 'syl', [L3(call), w.s([w.s([w.s([], 'fveq2', '( k = d -> ( C ` k ) = ( C ` d ) )')], 'fveq2d', '( k = d -> ( abs ` ( C ` k ) ) = ( abs ` ( C ` d ) ) )')],
                                                                       'breq1d', '( k = d -> ( ( abs ` ( C ` k ) ) <_ 1 <-> ( abs ` ( C ` d ) ) <_ 1 ) )')], 'rspcv' if False else 'idi', '') if False else
                                   D(w, X3, 'syl', [L3(call), w.s([w.s([w.s([w.s([], 'fveq2', '( k = d -> ( C ` k ) = ( C ` d ) )')], 'fveq2d', '( k = d -> ( abs ` ( C ` k ) ) = ( abs ` ( C ` d ) ) )')],
                                                                       'breq1d', '( k = d -> ( ( abs ` ( C ` k ) ) <_ 1 <-> ( abs ` ( C ` d ) ) <_ 1 ) )')], 'rspcv',
                                                                   '( d e. NN -> ( A. k e. NN ( abs ` ( C ` k ) ) <_ 1 -> ( abs ` ( C ` d ) ) <_ 1 ) )')], '') if False else None], '') if False else None
    rs = w.s([w.s([w.s([], 'fveq2', '( k = d -> ( C ` k ) = ( C ` d ) )')], 'fveq2d', '( k = d -> ( abs ` ( C ` k ) ) = ( abs ` ( C ` d ) ) )')],
             'breq1d', '( k = d -> ( ( abs ` ( C ` k ) ) <_ 1 <-> ( abs ` ( C ` d ) ) <_ 1 ) )')
    rsp = w.s([rs], 'rspcv', '( d e. NN -> ( A. k e. NN ( abs ` ( C ` k ) ) <_ 1 -> ( abs ` ( C ` d ) ) <_ 1 ) )')
    cd1 = D(w, X3, 'sylc', [c['d3'], L3(call), rsp], '( abs ` ( C ` d ) ) <_ 1')
    # |x| <_ |hBV|
    ahr = D(w, X3, 'abscld', [hc], '( abs ` %s ) e. RR' % HB)
    ah0 = D(w, X3, 'absge0d', [hc], '0 <_ ( abs ` %s )' % HB)
    acr = D(w, X3, 'abscld', [c['cd']], '( abs ` ( C ` d ) ) e. RR'); ac0 = D(w, X3, 'absge0d', [c['cd']], '0 <_ ( abs ` ( C ` d ) )')
    adr = D(w, X3, 'abscld', [dsc], '( abs ` ( d ^c -u S ) ) e. RR'); ad0 = D(w, X3, 'absge0d', [dsc], '0 <_ ( abs ` ( d ^c -u S ) )')
    e1 = D(w, X3, 'absmuld', [hcd, dsc], '( abs ` %s ) = ( ( abs ` ( %s x. ( C ` d ) ) ) x. ( abs ` ( d ^c -u S ) ) )' % (x, HB))
    e2 = D(w, X3, 'oveq1d', [D(w, X3, 'absmuld', [hc, c['cd']], '( abs ` ( %s x. ( C ` d ) ) ) = ( ( abs ` %s ) x. ( abs ` ( C ` d ) ) )' % (HB, HB))],
           '( ( abs ` ( %s x. ( C ` d ) ) ) x. ( abs ` ( d ^c -u S ) ) ) = ( ( ( abs ` %s ) x. ( abs ` ( C ` d ) ) ) x. ( abs ` ( d ^c -u S ) ) )' % (HB, HB))
    m1 = D(w, X3, 'lemul12ad', [ahr, ahr, acr, a1(w, X3, '1re', '1 e. RR'), ah0, D(w, X3, 'leidd', [ahr], '( abs ` %s ) <_ ( abs ` %s )' % (HB, HB)), ac0, cd1],
           '( ( abs ` %s ) x. ( abs ` ( C ` d ) ) ) <_ ( ( abs ` %s ) x. 1 )' % (HB, HB))
    p1r = D(w, X3, 'remulcld', [ahr, acr], '( ( abs ` %s ) x. ( abs ` ( C ` d ) ) ) e. RR' % HB)
    m2 = D(w, X3, 'lemul12ad', [p1r, D(w, X3, 'remulcld', [ahr, a1(w, X3, '1re', '1 e. RR')], '( ( abs ` %s ) x. 1 ) e. RR' % HB), adr, a1(w, X3, '1re', '1 e. RR'),
                                D(w, X3, 'mulge0d', [ahr, acr, ah0, ac0], '0 <_ ( ( abs ` %s ) x. ( abs ` ( C ` d ) ) )' % HB), m1, ad0, ds1],
           '( ( ( abs ` %s ) x. ( abs ` ( C ` d ) ) ) x. ( abs ` ( d ^c -u S ) ) ) <_ ( ( ( abs ` %s ) x. 1 ) x. 1 )' % (HB, HB))
    ahc = D(w, X3, 'recnd', [ahr], '( abs ` %s ) e. CC' % HB)
    e3 = D(w, X3, 'eqtrd', [D(w, X3, 'mulridd', [D(w, X3, 'mulcld', [ahc, D(w, X3, '1cnd', [], '1 e. CC')], '( ( abs ` %s ) x. 1 ) e. CC' % HB)], '( ( ( abs ` %s ) x. 1 ) x. 1 ) = ( ( abs ` %s ) x. 1 )' % (HB, HB)),
                            D(w, X3, 'mulridd', [ahc], '( ( abs ` %s ) x. 1 ) = ( abs ` %s )' % (HB, HB))], '( ( ( abs ` %s ) x. 1 ) x. 1 ) = ( abs ` %s )' % (HB, HB))
    xb = chain(w, X3, ['( abs ` %s )' % x, '( ( abs ` ( %s x. ( C ` d ) ) ) x. ( abs ` ( d ^c -u S ) ) )' % HB,
                       '( ( ( abs ` %s ) x. ( abs ` ( C ` d ) ) ) x. ( abs ` ( d ^c -u S ) ) )' % HB, '( ( ( abs ` %s ) x. 1 ) x. 1 )' % HB, '( abs ` %s )' % HB],
               [e1, e2, m2, e3], ['=', '=', '<_', '='])
    # level d
    DV = c['DV']
    SD = 'sum_ d e. %s %s' % (DV, x)
    SH = 'sum_ d e. %s ( abs ` %s )' % (DV, HB)
    sdc = D(w, X2, 'fsumcl', [c['dvf'], xc], '%s e. CC' % SD)
    a1_ = D(w, X2, 'fsumabs', [c['dvf'], xc], '( abs ` %s ) <_ sum_ d e. %s ( abs ` %s )' % (SD, DV, x))
    a2_ = D(w, X2, 'fsumle', [c['dvf'], D(w, X3, 'abscld', [xc], '( abs ` %s ) e. RR' % x), ahr, xb], 'sum_ d e. %s ( abs ` %s ) <_ %s' % (DV, x, SH))
    shr = D(w, X2, 'fsumrecl', [c['dvf'], ahr], '%s e. RR' % SH)
    sh0 = D(w, X2, 'fsumge0', [c['dvf'], ahr, ah0], '0 <_ %s' % SH)
    sdb = D(w, X2, 'letrd', [D(w, X2, 'abscld', [sdc], '( abs ` %s ) e. RR' % SD), D(w, X2, 'fsumrecl', [c['dvf'], D(w, X3, 'abscld', [xc], '( abs ` %s ) e. RR' % x)], 'sum_ d e. %s ( abs ` %s ) e. RR' % (DV, x)),
                             shr, a1_, a2_], '( abs ` %s ) <_ %s' % (SD, SH))
    # level t: a = 1 / ( r t )
    A_ = '( 1 / ( r x. t ) )'
    rtc = D(w, X2, 'nncnd', [c['rt2']], '( r x. t ) e. CC')
    ar_ = D(w, X2, 'nnrecred', [c['rt2']], '%s e. RR' % A_)
    a0_ = D(w, X2, 'ltled', [a1(w, X2, '0re', '0 e. RR'), ar_, D(w, X2, 'syl', [c['rt2'], w.inst('nnrecgt0')], '0 < %s' % A_)], '0 <_ %s' % A_)
    ac_ = D(w, X2, 'recnd', [ar_], '%s e. CC' % A_)
    T2 = '( %s x. %s )' % (A_, SD)
    t2c = D(w, X2, 'mulcld', [ac_, sdc], '%s e. CC' % T2)
    t2a = D(w, X2, 'eqtrd', [D(w, X2, 'absmuld', [ac_, sdc], '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (T2, A_, SD)),
                             D(w, X2, 'oveq1d', [D(w, X2, 'absidd', [ar_, a0_], '( abs ` %s ) = %s' % (A_, A_))], '( ( abs ` %s ) x. ( abs ` %s ) ) = ( %s x. ( abs ` %s ) )' % (A_, SD, A_, SD))],
            '( abs ` %s ) = ( %s x. ( abs ` %s ) )' % (T2, A_, SD))
    t2b = D(w, X2, 'lemul2ad', [D(w, X2, 'abscld', [sdc], '( abs ` %s ) e. RR' % SD), shr, ar_, a0_, sdb], '( %s x. ( abs ` %s ) ) <_ ( %s x. %s )' % (A_, SD, A_, SH))
    T2H = '( %s x. %s )' % (A_, SH)
    t2 = D(w, X2, 'eqbrtrd', [t2a, t2b], '( abs ` %s ) <_ %s' % (T2, T2H))
    t2hr = D(w, X2, 'remulcld', [ar_, shr], '%s e. RR' % T2H)
    t2h0 = D(w, X2, 'mulge0d', [ar_, shr, a0_, sh0], '0 <_ %s' % T2H)
    RSs = c['RSs']
    rsf1 = lift(w, c['rsf'], X1)
    ST = 'sum_ t e. %s %s' % (RSs, T2)
    STH = 'sum_ t e. %s %s' % (RSs, T2H)
    stc = D(w, X1, 'fsumcl', [rsf1, t2c], '%s e. CC' % ST)
    b1 = D(w, X1, 'fsumabs', [rsf1, t2c], '( abs ` %s ) <_ sum_ t e. %s ( abs ` %s )' % (ST, RSs, T2))
    b2 = D(w, X1, 'fsumle', [rsf1, D(w, X2, 'abscld', [t2c], '( abs ` %s ) e. RR' % T2), t2hr, t2], 'sum_ t e. %s ( abs ` %s ) <_ %s' % (RSs, T2, STH))
    sthr = D(w, X1, 'fsumrecl', [rsf1, t2hr], '%s e. RR' % STH)
    stb = D(w, X1, 'letrd', [D(w, X1, 'abscld', [stc], '( abs ` %s ) e. RR' % ST), D(w, X1, 'fsumrecl', [rsf1, D(w, X2, 'abscld', [t2c], '( abs ` %s ) e. RR' % T2)], 'sum_ t e. %s ( abs ` %s ) e. RR' % (RSs, T2)),
                             sthr, b1, b2], '( abs ` %s ) <_ %s' % (ST, STH))
    SR = 'sum_ r e. %s %s' % (RSs, ST)
    SRH = 'sum_ r e. %s %s' % (RSs, STH)
    src = d('fsumcl', [c['rsf'], stc], '%s e. CC' % SR)
    c1 = d('fsumabs', [c['rsf'], stc], '( abs ` %s ) <_ sum_ r e. %s ( abs ` %s )' % (SR, RSs, ST))
    c2 = d('fsumle', [c['rsf'], D(w, X1, 'abscld', [stc], '( abs ` %s ) e. RR' % ST), sthr, stb], 'sum_ r e. %s ( abs ` %s ) <_ %s' % (RSs, ST, SRH))
    fb = d('letrd', [d('abscld', [src], '( abs ` %s ) e. RR' % SR), d('fsumrecl', [c['rsf'], D(w, X1, 'abscld', [stc], '( abs ` %s ) e. RR' % ST)], 'sum_ r e. %s ( abs ` %s ) e. RR' % (RSs, ST)),
                     d('fsumrecl', [c['rsf'], sthr], '%s e. RR' % SRH), c1, c2], '( abs ` %s ) <_ %s' % (SR, SRH))
    assert SR == MH('N', 'R', 'C', 'S'), (SR, MH('N', 'R', 'C', 'S'))
    assert SRH == HM('N', 'R'), (SRH, HM('N', 'R'))
    fin = d('jca', [src, fb], CONC)
    w.qed([fin], 'idi', S['gf1mhb'])
    return run(w, only)


def gen_hm():
    w = W('gf1hm', 'The coefficient mass, log-free: ` 0 <_ Hmass <_ CTau ^ 2 R ^ ( 801 / 400 ) ` for ` 1 <_ R ` (Lean ` Hmass_nonneg ` , ` Hmass_le ` , ` Hmass_le_sq ` , ` prod_primeFactors_add_one_le_two_pow_mul ` ; ~ z5hbvabs , ~ z6omg , ~ sqfprodid ).')
    X0, CONC = split_imp(S['gf1hm'])
    d = mk(w, X0)
    nv = proj(w, X0, 'N e. V'); rr = proj(w, X0, 'R e. RR'); r1_ = proj(w, X0, '1 <_ R')
    RSs = RS('N', 'R')
    rs = d('syl', [d('jca', [nv, rr], '( N e. V /\\ R e. RR )'), w.inst('z5rsetfi')], '( %s C_ ( 1 ... ( |_ ` R ) ) /\\ %s e. Fin )' % (RSs, RSs))
    rsf = d('simprd', [rs], '%s e. Fin' % RSs)
    def elr(X, v):
        """( X -> ( v e. NN /\\ ( mmu ` v ) =/= 0 /\\ v <_ R ) ) for v e. RS a conjunct of X"""
        dx = mk(w, X)
        vin = proj(w, X, '%s e. %s' % (v, RSs))
        e = dx('mpbid', [vin, dx('syl', [lift(w, d('jca', [nv, rr], '( N e. V /\\ R e. RR )'), X), w.inst('z5elrset')],
                                 '( %s e. %s <-> ( %s e. ( 1 ... ( |_ ` R ) ) /\\ ( ( mmu ` %s ) =/= 0 /\\ ( %s gcd N ) = 1 ) ) )' % (v, RSs, v, v, v))],
                 '( %s e. ( 1 ... ( |_ ` R ) ) /\\ ( ( mmu ` %s ) =/= 0 /\\ ( %s gcd N ) = 1 ) )' % (v, v, v))
        fz = dx('simpld', [e], '%s e. ( 1 ... ( |_ ` R ) )' % v)
        vn = dx('syl', [fz, w.inst('elfznn')], '%s e. NN' % v)
        mu = dx('simprld' if False else 'simpld', [dx('simprd', [e], '( ( mmu ` %s ) =/= 0 /\\ ( %s gcd N ) = 1 )' % (v, v))], '( mmu ` %s ) =/= 0' % v)
        vf = dx('elfzle2' if False else 'syl', [fz, w.inst('elfzle2')], '%s <_ ( |_ ` R )' % v)
        vR = dx('letrd', [dx('nnred', [vn], '%s e. RR' % v), dx('syl', [lift(w, rr, X), w.inst('reflcl')], '( |_ ` R ) e. RR'), lift(w, rr, X), vf,
                          dx('syl', [lift(w, rr, X), w.inst('flle')], '( |_ ` R ) <_ R')], '%s <_ R' % v)
        return vn, mu, vR
    X1 = '( %s /\\ r e. %s )' % (X0, RSs)
    X2 = '( %s /\\ t e. %s )' % (X1, RSs)
    rn1, mr1, rR1 = elr(X1, 'r')
    tn2, mt2, tR2 = elr(X2, 't')
    rn2 = lift(w, rn1, X2); mr2 = lift(w, mr1, X2)
    Pq = lambda v: '{ q e. Prime | q || %s }' % v
    PP = lambda v: 'prod_ p e. %s ( p + 1 )' % Pq(v)
    AR = lambda v: '( ( 1 / %s ) x. %s )' % (v, PP(v))
    HS = 'sum_ d e. %s ( abs ` ( ( r hBV t ) ` d ) )' % DIV('( r x. t )')
    # prod facts for v (under X, v e. NN, squarefree)
    def pfacts(X, v, vn, mu):
        dx = mk(w, X)
        pf = dx('syl', [vn, w.inst('prmdvdsfi')], '%s e. Fin' % Pq(v))
        Xp = '( %s /\\ p e. %s )' % (X, Pq(v))
        dp = mk(w, Xp)
        pp = dp('simpld', [dp('mpbid', [w.s([], 'simpr', '( %s -> p e. %s )' % (Xp, Pq(v))), a1(w, Xp, 'elrab', '( p e. %s <-> ( p e. Prime /\\ p || %s ) )' % (Pq(v), v), [w.s([], 'breq1', '( q = p -> ( q || %s <-> p || %s ) )' % (v, v))])],
                                      '( p e. Prime /\\ p || %s )' % v)], 'p e. Prime')
        pn = dp('syl', [pp, w.inst('prmnn')], 'p e. NN')
        pr = dp('nnred', [pn], 'p e. RR')
        p1r = dp('peano2red' if False else 'readdcld', [pr, a1(w, Xp, '1re', '1 e. RR')], '( p + 1 ) e. RR')
        cl = Closure(w, Xp, {'p': pr})
        p10 = lin.linarith(w, Xp, [dp('nnge1d', [pn], '1 <_ p')], '0 <_ ( p + 1 )', closure=cl)
        p2 = lin.linarith(w, Xp, [dp('nnge1d', [pn], '1 <_ p')], '( p + 1 ) <_ ( 2 x. p )', closure=cl)
        tp = dp('remulcld', [a1(w, Xp, '2re', '2 e. RR'), pr], '( 2 x. p ) e. RR')
        le = dx('fprodle', [w.s([], 'nfv', 'F/ p %s' % X), pf, p1r, p10, tp, p2], '%s <_ prod_ p e. %s ( 2 x. p )' % (PP(v), Pq(v)))
        pm = dx('fprodmul', [pf, a1(w, Xp, '2cn', '2 e. CC'), dp('nncnd', [pn], 'p e. CC')], 'prod_ p e. %s ( 2 x. p ) = ( prod_ p e. %s 2 x. prod_ p e. %s p )' % (Pq(v), Pq(v), Pq(v)))
        pc = dx('syl2anc', [pf, a1(w, X, '2cn', '2 e. CC'), w.inst('fprodconst')], 'prod_ p e. %s 2 = ( 2 ^ ( # ` %s ) )' % (Pq(v), Pq(v)))
        pi = dx('syl', [dx('jca', [vn, mu], '( %s e. NN /\\ ( mmu ` %s ) =/= 0 )' % (v, v)), w.inst('sqfprodid')], 'prod_ p e. %s p = %s' % (Pq(v), v))
        TW = '( 2 ^ ( # ` %s ) )' % Pq(v)
        eqp = dx('eqtrd', [pm, dx('oveq12d', [pc, pi], '( prod_ p e. %s 2 x. prod_ p e. %s p ) = ( %s x. %s )' % (Pq(v), Pq(v), TW, v))],
                 'prod_ p e. %s ( 2 x. p ) = ( %s x. %s )' % (Pq(v), TW, v))
        ppb = dx('breqtrd', [le, eqp], '%s <_ ( %s x. %s )' % (PP(v), TW, v))
        ppr = dx('fprodrecl' if False else 'fprodrecl', [pf, p1r], '%s e. RR' % PP(v))
        pp0 = dx('fprodge0', [w.s([], 'nfv', 'F/ p %s' % X), pf, p1r, p10], '0 <_ %s' % PP(v))
        return pf, ppb, ppr, pp0, TW
    import num as _num
    from mvlib import ringeq, ringeqp
    CT = 'CTau'
    ctn = a1(w, X0, 'eqeltri', 'CTau e. NN', [w.s([], 'df-ctau', 'CTau = ( 2 ^ ( 2 ^ ; ; 8 0 0 ) )'),
                                                w.s([w.s([], '2nn', '2 e. NN'), w.s([w.s([], '2nn0', '2 e. NN0'), _num.nn0(w, 800), w.inst('nn0expcl')], 'mp2an', '( 2 ^ ; ; 8 0 0 ) e. NN0'), w.inst('nnexpcl')], 'mp2an', '( 2 ^ ( 2 ^ ; ; 8 0 0 ) ) e. NN')])
    ctr = d('nnred', [ctn], 'CTau e. RR'); ct0 = d('ltled', [a1(w, X0, '0re', '0 e. RR'), ctr, d('nngt0d', [ctn], '0 < CTau')], '0 <_ CTau')
    E8 = '( 1 / ; ; 8 0 0 )'
    e8r = w.s([w.s([w.s([], '1re', '1 e. RR'), _num.re_nat(w, 800), _num.ne0_nat(w, 800)], 'redivcli', '%s e. RR' % E8)], 'a1i', '( %s -> %s e. RR )' % (X0, E8))
    e80 = d('ltled', [a1(w, X0, '0re', '0 e. RR'), e8r, w.s([w.s([_num.gt0_nat(w, 1) if False else w.s([], '1re', '1 e. RR'), _num.re_nat(w, 800), w.s([], '0lt1', '0 < 1'), _num.gt0_nat(w, 800)], 'divgt0ii', '0 < %s' % E8)], 'a1i', '( %s -> 0 < %s )' % (X0, E8))], '0 <_ %s' % E8)
    R0 = d('ltled', [a1(w, X0, '0re', '0 e. RR'), rr, d('ltletrd', [a1(w, X0, '0re', '0 e. RR'), a1(w, X0, '1re', '1 e. RR'), rr, a1(w, X0, '0lt1', '0 < 1'), r1_], '0 < R')], '0 <_ R')
    Rp = d('ltletrd', [a1(w, X0, '0re', '0 e. RR'), a1(w, X0, '1re', '1 e. RR'), rr, a1(w, X0, '0lt1', '0 < 1'), r1_], '0 < R')
    RE8 = '( R ^c %s )' % E8
    re8r = d('rpred', [d('rpcxpcld', [d('elrpd', [rr, Rp], 'R e. RR+'), e8r], '%s e. RR+' % RE8)], '%s e. RR' % RE8)
    re80 = d('ltled', [a1(w, X0, '0re', '0 e. RR'), re8r, d('rpgt0d', [d('rpcxpcld', [d('elrpd', [rr, Rp], 'R e. RR+'), e8r], '%s e. RR+' % RE8)], '0 < %s' % RE8)], '0 <_ %s' % RE8)
    K1 = '( CTau x. %s )' % RE8
    k1r = d('remulcld', [ctr, re8r], '%s e. RR' % K1); k10 = d('mulge0d', [ctr, re8r, ct0, re80], '0 <_ %s' % K1)
    def abound(X, v, vn, mu, vR):
        dx = mk(w, X)
        pf, ppb, ppr, pp0, TW = pfacts(X, v, vn, mu)
        vr = dx('nnred', [vn], '%s e. RR' % v); vc = dx('nncnd', [vn], '%s e. CC' % v); vne = dx('nnne0d', [vn], '%s =/= 0' % v)
        iv = '( 1 / %s )' % v
        ivr = dx('nnrecred', [vn], '%s e. RR' % iv)
        iv0 = dx('ltled', [a1(w, X, '0re', '0 e. RR'), ivr, dx('syl', [vn, w.inst('nnrecgt0')], '0 < %s' % iv)], '0 <_ %s' % iv)
        twr = dx('reexpcld' if False else 'remulcld', [a1(w, X, '2re', '2 e. RR'), a1(w, X, '1re', '1 e. RR')], '( 2 x. 1 ) e. RR') if False else None
        twn = dx('nnexpcld', [a1(w, X, '2nn', '2 e. NN'), dx('syl', [pf, w.inst('hashcl')], '( # ` %s ) e. NN0' % Pq(v))], '%s e. NN' % TW)
        twr = dx('nnred', [twn], '%s e. RR' % TW)
        m = dx('lemul2ad', [ppr, dx('remulcld', [twr, vr], '( %s x. %s ) e. RR' % (TW, v)), ivr, iv0, ppb], '( %s x. %s ) <_ ( %s x. ( %s x. %s ) )' % (iv, PP(v), iv, TW, v))
        ivc = dx('recnd', [ivr], '%s e. CC' % iv)
        cl = Closure(w, X, {TW: ('CC', dx('nncnd', [twn], '%s e. CC' % TW)), v: ('CC', vc), iv: ('CC', ivc)})
        for a_ in [TW, iv]:
            cl.atom(a_)
        r1 = ringeq(w, X, '( %s x. ( %s x. %s ) )' % (iv, TW, v), '( %s x. ( %s x. %s ) )' % (TW, v, iv), cl)
        r2 = dx('oveq2d', [dx('recidd', [vc, vne], '( %s x. %s ) = 1' % (v, iv))], '( %s x. ( %s x. %s ) ) = ( %s x. 1 )' % (TW, v, iv, TW))
        r3 = dx('mulridd', [dx('nncnd', [twn], '%s e. CC' % TW)], '( %s x. 1 ) = %s' % (TW, TW))
        OM = '( 2 ^ ( # ` { p e. Prime | p || %s } ) )' % v
        om = dx('syl', [vn, w.inst('z6omg')], '%s <_ ( CTau x. ( %s ^c %s ) )' % (OM, v, E8))
        cbr = w.s([w.s([], 'breq1', '( p = q -> ( p || %s <-> q || %s ) )' % (v, v))], 'cbvrabv', '{ p e. Prime | p || %s } = %s' % (v, Pq(v)))
        omeq = a1(w, X, 'oveq2i', '%s = %s' % (OM, TW), [w.s([cbr], 'fveq2i', '( # ` { p e. Prime | p || %s } ) = ( # ` %s )' % (v, Pq(v)))])
        om2 = dx('eqbrtrrd', [omeq, om], '%s <_ ( CTau x. ( %s ^c %s ) )' % (TW, v, E8))
        cx = dx('syl3anc', [dx('3jca', [vr, lift(w, rr, X), lift(w, e8r, X)], '( %s e. RR /\\ R e. RR /\\ %s e. RR )' % (v, E8)),
                            dx('jca', [dx('ltled', [a1(w, X, '0re', '0 e. RR'), vr, dx('nngt0d', [vn], '0 < %s' % v)], '0 <_ %s' % v), lift(w, e80, X)], '( 0 <_ %s /\\ 0 <_ %s )' % (v, E8)), vR, w.inst('cxple2a')],
                '( %s ^c %s ) <_ %s' % (v, E8, RE8))
        vE = dx('rpred', [dx('rpcxpcld', [dx('nnrpd', [vn], '%s e. RR+' % v), lift(w, e8r, X)], '( %s ^c %s ) e. RR+' % (v, E8))], '( %s ^c %s ) e. RR' % (v, E8))
        cm = dx('lemul2ad', [vE, lift(w, re8r, X), lift(w, ctr, X), lift(w, ct0, X), cx], '( CTau x. ( %s ^c %s ) ) <_ %s' % (v, E8, K1))
        TWb = dx('letrd', [twr, dx('remulcld', [lift(w, ctr, X), vE], '( CTau x. ( %s ^c %s ) ) e. RR' % (v, E8)), lift(w, k1r, X), om2, cm], '%s <_ %s' % (TW, K1))
        ab = chain(w, X, [AR(v), '( %s x. ( %s x. %s ) )' % (iv, TW, v), '( %s x. ( %s x. %s ) )' % (TW, v, iv), '( %s x. 1 )' % TW, TW], [m, r1, r2, r3], ['<_', '=', '=', '='])
        abnd = dx('letrd', [dx('remulcld', [ivr, ppr], '%s e. RR' % AR(v)), twr, lift(w, k1r, X), ab, TWb], '%s <_ %s' % (AR(v), K1))
        ar_ = dx('remulcld', [ivr, ppr], '%s e. RR' % AR(v))
        a0 = dx('mulge0d', [ivr, ppr, iv0, pp0], '0 <_ %s' % AR(v))
        return abnd, ar_, a0, ivr, iv0, ppr, pp0, ivc, vc, vne
    ab_r, ar_r, a0_r, ivr_r, iv0_r, ppr_r, pp0_r, ivc_r, vc_r, vne_r = abound(X1, 'r', rn1, mr1, rR1)
    ab_t, ar_t, a0_t, ivr_t, iv0_t, ppr_t, pp0_t, ivc_t, vc_t, vne_t = abound(X2, 't', tn2, mt2, tR2)
    d2 = mk(w, X2); L2 = lambda st: lift(w, st, X2)
    # term bound
    hb = d2('syl', [d2('jca', [d2('jca', [rn2, mr2], '( r e. NN /\\ ( mmu ` r ) =/= 0 )'), d2('jca', [tn2, mt2], '( t e. NN /\\ ( mmu ` t ) =/= 0 )')],
                       '( ( r e. NN /\\ ( mmu ` r ) =/= 0 ) /\\ ( t e. NN /\\ ( mmu ` t ) =/= 0 ) )'), w.inst('z5hbvabs')], '%s <_ ( %s x. %s )' % (HS, PP('r'), PP('t')))
    rt = d2('nnmulcld', [rn2, tn2], '( r x. t ) e. NN')
    IRT = '( 1 / ( r x. t ) )'
    irtr = d2('nnrecred', [rt], '%s e. RR' % IRT)
    irt0 = d2('ltled', [a1(w, X2, '0re', '0 e. RR'), irtr, d2('syl', [rt, w.inst('nnrecgt0')], '0 < %s' % IRT)], '0 <_ %s' % IRT)
    DVt = DIV('( r x. t )')
    dvf = d2('syl', [rt, w.inst('dvdsfi')], '%s e. Fin' % DVt)
    X3 = '( %s /\\ d e. %s )' % (X2, DVt)
    d3n = D(w, X3, 'simpld', [D(w, X3, 'sylib', [w.s([], 'simpr', '( %s -> d e. %s )' % (X3, DVt)), w.s([w.s([], 'breq1', '( x = d -> ( x || ( r x. t ) <-> d || ( r x. t ) ) )')], 'elrab', '( d e. %s <-> ( d e. NN /\\ d || ( r x. t ) ) )' % DVt)],
                                        '( d e. NN /\\ d || ( r x. t ) )')], 'd e. NN')
    hvc = D(w, X3, 'recnd', [D(w, X3, 'syl', [D(w, X3, 'jca', [D(w, X3, 'jca', [lift(w, rn2, X3), lift(w, tn2, X3)], '( r e. NN /\\ t e. NN )'), d3n], '( ( r e. NN /\\ t e. NN ) /\\ d e. NN )'), w.inst('z5hbvre')],
                                        '( ( r hBV t ) ` d ) e. RR')], '( ( r hBV t ) ` d ) e. CC')
    habr = D(w, X3, 'abscld', [hvc], '( abs ` ( ( r hBV t ) ` d ) ) e. RR'); hab0 = D(w, X3, 'absge0d', [hvc], '0 <_ ( abs ` ( ( r hBV t ) ` d ) )')
    hsr = d2('fsumrecl', [dvf, habr], '%s e. RR' % HS); hs0 = d2('fsumge0', [dvf, habr, hab0], '0 <_ %s' % HS)
    TERM = '( %s x. %s )' % (IRT, HS)
    termr = d2('remulcld', [irtr, hsr], '%s e. RR' % TERM); term0 = d2('mulge0d', [irtr, hsr, irt0, hs0], '0 <_ %s' % TERM)
    tb1 = d2('lemul2ad', [hsr, d2('remulcld', [ppr_r if False else L2(ppr_r), ppr_t], '( %s x. %s ) e. RR' % (PP('r'), PP('t'))), irtr, irt0, hb], '%s <_ ( %s x. ( %s x. %s ) )' % (TERM, IRT, PP('r'), PP('t')))
    dmd = d2('divmuldivd', [d2('1cnd', [], '1 e. CC'), L2(vc_r), d2('1cnd', [], '1 e. CC'), vc_t, L2(vne_r), vne_t], '( ( 1 / r ) x. ( 1 / t ) ) = ( ( 1 x. 1 ) / ( r x. t ) )')
    irt_eq = d2('eqtrd', [dmd, d2('oveq1d', [a1(w, X2, '1t1e1', '( 1 x. 1 ) = 1')], '( ( 1 x. 1 ) / ( r x. t ) ) = %s' % IRT)], '( ( 1 / r ) x. ( 1 / t ) ) = %s' % IRT)
    clp = Closure(w, X2, {'( 1 / r )': ('CC', L2(ivc_r)), '( 1 / t )': ('CC', ivc_t), PP('r'): ('CC', d2('recnd', [L2(ppr_r)], '%s e. CC' % PP('r'))), PP('t'): ('CC', d2('recnd', [ppr_t], '%s e. CC' % PP('t')))})
    for a_ in ['( 1 / r )', '( 1 / t )', PP('r'), PP('t')]:
        clp.atom(a_)
    tq1 = d2('oveq1d', [d2('eqcomd', [irt_eq], '%s = ( ( 1 / r ) x. ( 1 / t ) )' % IRT)], '( %s x. ( %s x. %s ) ) = ( ( ( 1 / r ) x. ( 1 / t ) ) x. ( %s x. %s ) )' % (IRT, PP('r'), PP('t'), PP('r'), PP('t')))
    tq2 = ringeq(w, X2, '( ( ( 1 / r ) x. ( 1 / t ) ) x. ( %s x. %s ) )' % (PP('r'), PP('t')), '( %s x. %s )' % (AR('r'), AR('t')), clp)
    tb = chain(w, X2, [TERM, '( %s x. ( %s x. %s ) )' % (IRT, PP('r'), PP('t')), '( ( ( 1 / r ) x. ( 1 / t ) ) x. ( %s x. %s ) )' % (PP('r'), PP('t')), '( %s x. %s )' % (AR('r'), AR('t'))],
               [tb1, tq1, tq2], ['<_', '=', '='])
    art = d2('remulcld', [L2(ar_r), ar_t], '( %s x. %s ) e. RR' % (AR('r'), AR('t')))
    rsf1 = lift(w, rsf, X1)
    s1 = D(w, X1, 'fsumle', [rsf1, termr, art, tb], 'sum_ t e. %s %s <_ sum_ t e. %s ( %s x. %s )' % (RSs, TERM, RSs, AR('r'), AR('t')))
    s1l = D(w, X1, 'fsumrecl', [rsf1, termr], 'sum_ t e. %s %s e. RR' % (RSs, TERM))
    s1r = D(w, X1, 'fsumrecl', [rsf1, art], 'sum_ t e. %s ( %s x. %s ) e. RR' % (RSs, AR('r'), AR('t')))
    s10 = D(w, X1, 'fsumge0', [rsf1, termr, term0], '0 <_ sum_ t e. %s %s' % (RSs, TERM))
    s2 = d('fsumle', [rsf, s1l, s1r, s1], '%s <_ sum_ r e. %s sum_ t e. %s ( %s x. %s )' % (HM('N', 'R'), RSs, RSs, AR('r'), AR('t')))
    hm0 = d('fsumge0', [rsf, s1l, s10], '0 <_ %s' % HM('N', 'R'))
    SA = 'sum_ r e. %s %s' % (RSs, AR('r'))
    f2m = d('fsum2mul', [rsf, rsf, D(w, X1, 'recnd', [ar_r], '%s e. CC' % AR('r')), D(w, '( %s /\\ t e. %s )' % (X0, RSs), 'recnd', [lift(w, ar_t, X2) if False else None], '') if False else None], '') if False else None
    # a_t e. CC under ( X0 /\\ t e. RS ) directly from the r-version by renaming is heavy; use fsum2mul with the t-context
    Xt = '( %s /\\ t e. %s )' % (X0, RSs)
    tn_t, mt_t, tR_t = elr(Xt, 't')
    abt_t, art_t, a0t_t, _, _, _, _, _, _, _ = abound(Xt, 't', tn_t, mt_t, tR_t)
    f2m = d('fsum2mul', [rsf, rsf, D(w, X1, 'recnd', [ar_r], '%s e. CC' % AR('r')), D(w, Xt, 'recnd', [art_t], '%s e. CC' % AR('t'))],
            'sum_ r e. %s sum_ t e. %s ( %s x. %s ) = ( %s x. sum_ t e. %s %s )' % (RSs, RSs, AR('r'), AR('t'), SA, RSs, AR('t')))
    at_ar = w.s([w.s([w.s([], 'oveq2', '( t = r -> ( 1 / t ) = ( 1 / r ) )'),
                      w.s([w.s([w.s([], 'breq2', '( t = r -> ( q || t <-> q || r ) )')], 'rabbidv', '( t = r -> %s = %s )' % (Pq('t'), Pq('r')))], 'prodeq1d', '( t = r -> %s = %s )' % (PP('t'), PP('r')))],
                     'oveq12d', '( t = r -> %s = %s )' % (AR('t'), AR('r')))], 'cbvsumv', 'sum_ t e. %s %s = %s' % (RSs, AR('t'), SA))
    sq = d('eqtrd', [f2m, d('oveq2d', [a1(w, X0, 'eqid' if False else 'idi', 'sum_ t e. %s %s = %s' % (RSs, AR('t'), SA), [at_ar])], '( %s x. sum_ t e. %s %s ) = ( %s x. %s )' % (SA, RSs, AR('t'), SA, SA))],
            'sum_ r e. %s sum_ t e. %s ( %s x. %s ) = ( %s x. %s )' % (RSs, RSs, AR('r'), AR('t'), SA, SA))
    # sum a_r <_ K
    sar = d('fsumrecl', [rsf, ar_r], '%s e. RR' % SA); sa0 = d('fsumge0', [rsf, ar_r, a0_r], '0 <_ %s' % SA)
    sb1 = d('fsumle', [rsf, ar_r, lift(w, k1r, X1), ab_r], '%s <_ sum_ r e. %s %s' % (SA, RSs, K1))
    sc = d('syl2anc', [rsf, d('recnd', [k1r], '%s e. CC' % K1), w.inst('fsumconst')], 'sum_ r e. %s %s = ( ( # ` %s ) x. %s )' % (RSs, K1, RSs, K1))
    hsh = d('syl', [rsf, w.inst('hashcl')], '( # ` %s ) e. NN0' % RSs)
    card = d('letrd', [d('nn0red', [hsh], '( # ` %s ) e. RR' % RSs), d('syl', [rr, w.inst('reflcl')], '( |_ ` R ) e. RR'), rr,
                       d('syl', [d('jca', [nv, d('jca', [rr, R0], '( R e. RR /\\ 0 <_ R )')], '( N e. V /\\ ( R e. RR /\\ 0 <_ R ) )'), w.inst('z5rsetcard')], '( # ` %s ) <_ ( |_ ` R )' % RSs),
                       d('syl', [rr, w.inst('flle')], '( |_ ` R ) <_ R')], '( # ` %s ) <_ R' % RSs)
    sb2 = d('lemul1ad', [d('nn0red', [hsh], '( # ` %s ) e. RR' % RSs), rr, k1r, k10, card], '( ( # ` %s ) x. %s ) <_ ( R x. %s )' % (RSs, K1, K1))
    E801 = '( ; ; 8 0 1 / ; ; 8 0 0 )'
    rc = d('recnd', [rr], 'R e. CC'); rne = d('gt0ne0d', [rr, Rp], 'R =/= 0') if False else d('rpne0d', [d('elrpd', [rr, Rp], 'R e. RR+')], 'R =/= 0')
    e8c = d('recnd', [e8r], '%s e. CC' % E8)
    num1 = lin.lineq(w, X0, '( 1 + %s )' % E8, E801, [], closure=Closure(w, X0))
    ca = d('cxpaddd', [rc, rne, d('1cnd', [], '1 e. CC'), e8c], '( R ^c ( 1 + %s ) ) = ( ( R ^c 1 ) x. %s )' % (E8, RE8))
    RE801 = '( R ^c %s )' % E801
    ca2 = d('eqtrd', [d('eqtr3d', [d('oveq2d', [num1], '( R ^c ( 1 + %s ) ) = %s' % (E8, RE801)), ca], '%s = ( ( R ^c 1 ) x. %s )' % (RE801, RE8)),
                      d('oveq1d', [d('syl', [rc, w.inst('cxp1')], '( R ^c 1 ) = R')], '( ( R ^c 1 ) x. %s ) = ( R x. %s )' % (RE8, RE8))], '%s = ( R x. %s )' % (RE801, RE8))
    K = '( CTau x. %s )' % RE801
    clk = Closure(w, X0, {'R': ('CC', rc), 'CTau': ('CC', d('nncnd', [ctn], 'CTau e. CC')), RE8: ('CC', d('recnd', [re8r], '%s e. CC' % RE8))})
    clk.atom(RE8)
    rk = d('eqtrd', [ringeq(w, X0, '( R x. %s )' % K1, '( CTau x. ( R x. %s ) )' % RE8, clk), d('oveq2d', [d('eqcomd', [ca2], '( R x. %s ) = %s' % (RE8, RE801))], '( CTau x. ( R x. %s ) ) = %s' % (RE8, K))],
            '( R x. %s ) = %s' % (K1, K))
    p1 = chain(w, X0, [SA, 'sum_ r e. %s %s' % (RSs, K1), '( ( # ` %s ) x. %s )' % (RSs, K1)], [sb1, sc], ['<_', '='])
    p2 = d('letrd', [d('fsumrecl', [rsf, ar_r], '%s e. RR' % SA), d('remulcld', [d('nn0red', [hsh], '( # ` %s ) e. RR' % RSs), k1r], '( ( # ` %s ) x. %s ) e. RR' % (RSs, K1)),
                     d('remulcld', [rr, k1r], '( R x. %s ) e. RR' % K1), p1, sb2], '%s <_ ( R x. %s )' % (SA, K1))
    sab = d('breqtrd', [p2, rk], '%s <_ %s' % (SA, K))
    re801r = d('rpred', [d('rpcxpcld', [d('elrpd', [rr, Rp], 'R e. RR+'), a1(w, X0, 'ax-mp' if False else 'eqid', '') if False else w.s([w.s([_num.re_nat(w, 801), _num.re_nat(w, 800), _num.ne0_nat(w, 800)], 'redivcli', '%s e. RR' % E801)], 'a1i', '( %s -> %s e. RR )' % (X0, E801))], '%s e. RR+' % RE801)], '%s e. RR' % RE801)
    kr = d('remulcld', [ctr, re801r], '%s e. RR' % K)
    sq2 = d('lemul12ad', [sar, kr, sar, kr, sa0, sab, sa0, sab], '( %s x. %s ) <_ ( %s x. %s )' % (SA, SA, K, K))
    E401 = '( ; ; 8 0 1 / ; ; 4 0 0 )'
    num2 = lin.lineq(w, X0, '( %s + %s )' % (E801, E801), E401, [], closure=Closure(w, X0))
    e801c = d('recnd', [w.s([w.s([_num.re_nat(w, 801), _num.re_nat(w, 800), _num.ne0_nat(w, 800)], 'redivcli', '%s e. RR' % E801)], 'a1i', '( %s -> %s e. RR )' % (X0, E801))], '%s e. CC' % E801)
    cb2 = d('cxpaddd', [rc, rne, e801c, e801c], '( R ^c ( %s + %s ) ) = ( %s x. %s )' % (E801, E801, RE801, RE801))
    RE401 = '( R ^c %s )' % E401
    cb3 = d('eqtr3d', [d('oveq2d', [num2], '( R ^c ( %s + %s ) ) = %s' % (E801, E801, RE401)), cb2], '%s = ( %s x. %s )' % (RE401, RE801, RE801))
    clk2 = Closure(w, X0, {'CTau': ('CC', d('nncnd', [ctn], 'CTau e. CC')), RE801: ('CC', d('recnd', [re801r], '%s e. CC' % RE801))})
    clk2.atom(RE801)
    kk = ringeqp(w, X0, '( %s x. %s )' % (K, K), '( ( CTau ^ 2 ) x. ( %s x. %s ) )' % (RE801, RE801), clk2)
    kk2 = d('eqtrd', [kk, d('oveq2d', [d('eqcomd', [cb3], '( %s x. %s ) = %s' % (RE801, RE801, RE401))], '( ( CTau ^ 2 ) x. ( %s x. %s ) ) = ( ( CTau ^ 2 ) x. %s )' % (RE801, RE801, RE401))],
              '( %s x. %s ) = ( ( CTau ^ 2 ) x. %s )' % (K, K, RE401))
    hb_ = chain(w, X0, [HM('N', 'R'), 'sum_ r e. %s sum_ t e. %s ( %s x. %s )' % (RSs, RSs, AR('r'), AR('t')), '( %s x. %s )' % (SA, SA)], [s2, sq], ['<_', '='])
    hbt = d('letrd', [d('fsumrecl', [rsf, s1l], '%s e. RR' % HM('N', 'R')), d('remulcld', [sar, sar], '( %s x. %s ) e. RR' % (SA, SA)), d('remulcld', [kr, kr], '( %s x. %s ) e. RR' % (K, K)), hb_, sq2],
             '%s <_ ( %s x. %s )' % (HM('N', 'R'), K, K))
    fin0 = d('breqtrd', [hbt, kk2], '%s <_ ( ( CTau ^ 2 ) x. %s )' % (HM('N', 'R'), RE401))
    fin = d('jca', [hm0, fin0], CONC)
    w.qed([fin], 'idi', S['gf1hm'])
    return run(w, only)


if __name__ == '__main__':
    gen_hbv0()
    gen_hbvs()
    gen_mhh()
    gen_mhb()
    gen_hm()
