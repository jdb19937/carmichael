"""Sortie GF1, section H: series helpers and Halasz duality (gf1cvadd, gf1ser, gf1hal).
MM_DB=sorties/gf1.mm MM_ENGINE=mmatch python3 tools/gen/gf1_h.py [LABEL...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from gf1lib import *

only = sys.argv[1:]
S['gf1cvadd.1'] = '( ( ph /\\ n e. NN ) -> ( F ` n ) e. CC )'
S['gf1cvadd.2'] = '( ( ph /\\ n e. NN ) -> ( G ` n ) e. CC )'
S['gf1cvadd.3'] = '( ph -> seq 1 ( + , F ) e. dom ~~> )'
S['gf1cvadd.4'] = '( ph -> seq 1 ( + , G ) e. dom ~~> )'
S['gf1cvadd'] = '( ph -> seq 1 ( + , ( m e. NN |-> ( ( F ` m ) + ( G ` m ) ) ) ) e. dom ~~> )'
S['gf1ser.1'] = '( ( ph /\\ n e. NN ) -> ( F ` n ) e. CC )'
S['gf1ser.2'] = '( ph -> seq 1 ( + , F ) e. dom ~~> )'
S['gf1ser'] = '( ph -> ( m e. NN |-> sum_ n e. ( 1 ... m ) ( F ` n ) ) ~~> sum_ n e. NN ( F ` n ) )'


def serval(w, Ak, kv, Fn, h):
    """under Akj = ( Ak /\\ n e. ( 1 ... kv ) ): n e. NN and ( Fn ` n ) e. CC from h ( ( ph /\\ n e. NN ) -> ( Fn ` n ) e. CC ); and ( seq ` kv ) e. CC under Ak"""
    Akj = '( %s /\\ n e. ( 1 ... %s ) )' % (Ak, kv)
    nn_ = D(w, Akj, 'syl', [w.s([], 'simpr', '( %s -> n e. ( 1 ... %s ) )' % (Akj, kv)), w.inst('elfznn')], 'n e. NN')
    fc = w.s([D(w, Akj, 'jca', [w.s([], 'simpll', '( %s -> ph )' % Akj), nn_], '( ph /\\ n e. NN )'), h], 'syl', '( %s -> ( %s ` n ) e. CC )' % (Akj, Fn))
    return Akj, nn_, fc


def seqcc(w, Ak, kv, kuz, Fn, fc, Akj):
    fs = D(w, Ak, 'fsumser', [w.s([], 'eqidd', '( %s -> ( %s ` n ) = ( %s ` n ) )' % (Akj, Fn, Fn)), kuz, fc], 'sum_ n e. ( 1 ... %s ) ( %s ` n ) = ( seq 1 ( + , %s ) ` %s )' % (kv, Fn, Fn, kv))
    return D(w, Ak, 'eqeltrrd', [fs, D(w, Ak, 'fsumcl', [D(w, Ak, 'fzfid', [], '( 1 ... %s ) e. Fin' % kv), fc], 'sum_ n e. ( 1 ... %s ) ( %s ` n ) e. CC' % (kv, Fn))],
             '( seq 1 ( + , %s ) ` %s ) e. CC' % (Fn, kv)), fs


def gen_cvadd():
    w = W('gf1cvadd', 'The sum of two convergent series converges ( ~ seradd , ~ climadd ).')
    h1, h2, h3, h4 = ehyps(w, 'gf1cvadd')
    A_ = 'ph'
    d = mk(w, A_)
    H = '( m e. NN |-> ( ( F ` m ) + ( G ` m ) ) )'
    SF = 'seq 1 ( + , F )'; SG = 'seq 1 ( + , G )'; SH = 'seq 1 ( + , %s )' % H
    ca = d('sylib', [h3, w.s([], 'climdm', '( %s e. dom ~~> <-> %s ~~> ( ~~> ` %s ) )' % (SF, SF, SF))], '%s ~~> ( ~~> ` %s )' % (SF, SF))
    cb = d('sylib', [h4, w.s([], 'climdm', '( %s e. dom ~~> <-> %s ~~> ( ~~> ` %s ) )' % (SG, SG, SG))], '%s ~~> ( ~~> ` %s )' % (SG, SG))
    nu = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
    one = a1(w, A_, '1z', '1 e. ZZ')
    Ak = '( ph /\\ k e. NN )'
    dk = mk(w, Ak)
    kuz = dk('eleqtrdi', [w.s([], 'simpr', '( %s -> k e. NN )' % Ak), nu], 'k e. ( ZZ>= ` 1 )')
    Akj, nnj, fcj = serval(w, Ak, 'k', 'F', h1)
    _, _, gcj = serval(w, Ak, 'k', 'G', h2)
    fgc = D(w, Akj, 'addcld', [fcj, gcj], '( ( F ` n ) + ( G ` n ) ) e. CC')
    hv = D(w, Akj, 'fvmptd', [w.s([], 'eqidd', '( %s -> %s = %s )' % (Akj, H, H)),
                              w.s([w.s([w.s([], 'fveq2', '( m = n -> ( F ` m ) = ( F ` n ) )'), w.s([], 'fveq2', '( m = n -> ( G ` m ) = ( G ` n ) )')], 'oveq12d',
                                       '( m = n -> ( ( F ` m ) + ( G ` m ) ) = ( ( F ` n ) + ( G ` n ) ) )')], 'adantl', '( ( %s /\\ m = n ) -> ( ( F ` m ) + ( G ` m ) ) = ( ( F ` n ) + ( G ` n ) ) )' % Akj),
                              nnj, fgc], '( %s ` n ) = ( ( F ` n ) + ( G ` n ) )' % H)
    sa = dk('seradd', [kuz, fcj, gcj, hv], '( %s ` k ) = ( ( %s ` k ) + ( %s ` k ) )' % (SH, SF, SG))
    sfc, _ = seqcc(w, Ak, 'k', kuz, 'F', fcj, Akj)
    sgc, _ = seqcc(w, Ak, 'k', kuz, 'G', gcj, Akj)
    cl = d('climadd', [nu, one, ca, a1(w, A_, 'seqex', '%s e. _V' % SH), cb, sfc, sgc, sa], '%s ~~> ( ( ~~> ` %s ) + ( ~~> ` %s ) )' % (SH, SF, SG))
    fin = w.s([w.s([], 'climrel', 'Rel ~~>'), cl, w.inst('releldm')], 'sylancr', S['gf1cvadd'])
    w.qed([fin], 'idi', S['gf1cvadd'])
    return run(w, only)


def gen_ser():
    w = W('gf1ser', 'The partial sums ` sum_ ( n <_ m ) F ( n ) ` of a convergent series converge to ` sum_ n e. NN F ( n ) ` ( ~ isumclim2 , ~ fsumser , ~ climeq ).')
    h1, h2 = ehyps(w, 'gf1ser')
    A_ = 'ph'
    d = mk(w, A_)
    nu = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
    one = a1(w, A_, '1z', '1 e. ZZ')
    SF = 'seq 1 ( + , F )'
    An = '( ph /\\ n e. NN )'
    ic = d('isumclim2', [nu, one, w.s([], 'eqidd', '( %s -> ( F ` n ) = ( F ` n ) )' % An), h1, h2], '%s ~~> sum_ n e. NN ( F ` n )' % SF)
    MP = '( m e. NN |-> sum_ n e. ( 1 ... m ) ( F ` n ) )'
    Am = '( ph /\\ k e. NN )'
    dm = mk(w, Am)
    min_ = w.s([], 'simpr', '( %s -> k e. NN )' % Am)
    muz = dm('eleqtrdi', [min_, nu], 'k e. ( ZZ>= ` 1 )')
    Amj, nnj, fcj = serval(w, Am, 'k', 'F', h1)
    sc, fs = seqcc(w, Am, 'k', muz, 'F', fcj, Amj)
    fsc = dm('fsumcl', [dm('fzfid', [], '( 1 ... k ) e. Fin'), fcj], 'sum_ n e. ( 1 ... k ) ( F ` n ) e. CC')
    sub = w.s([w.s([], 'oveq2', '( m = k -> ( 1 ... m ) = ( 1 ... k ) )')], 'sumeq1d', '( m = k -> sum_ n e. ( 1 ... m ) ( F ` n ) = sum_ n e. ( 1 ... k ) ( F ` n ) )')
    mv = dm('fvmptd', [w.s([], 'eqidd', '( %s -> %s = %s )' % (Am, MP, MP)), w.s([sub], 'adantl', '( ( %s /\\ m = k ) -> sum_ n e. ( 1 ... m ) ( F ` n ) = sum_ n e. ( 1 ... k ) ( F ` n ) )' % Am),
                       min_, fsc], '( %s ` k ) = sum_ n e. ( 1 ... k ) ( F ` n )' % MP)
    eqv = dm('eqtr4d', [dm('eqcomd', [fs], '( %s ` k ) = sum_ n e. ( 1 ... k ) ( F ` n )' % SF), mv], '( %s ` k ) = ( %s ` k )' % (SF, MP))
    ce = d('climeq', [nu, a1(w, A_, 'seqex', '%s e. _V' % SF), a1(w, A_, 'mptex', '%s e. _V' % MP, [w.s([], 'nnex', 'NN e. _V')]), one, eqv],
           '( %s ~~> sum_ n e. NN ( F ` n ) <-> %s ~~> sum_ n e. NN ( F ` n ) )' % (SF, MP))
    fin = d('mpbid', [ic, ce], '%s ~~> sum_ n e. NN ( F ` n )' % MP)
    w.qed([fin], 'idi', S['gf1ser'])
    return run(w, only)


ANc = 'if ( B = 0 , 0 , ( ( ( abs ` C ) ^ 2 ) / B ) )'
S['gf1anb'] = ('( ( C e. CC /\\ ( B e. RR /\\ 0 <_ B ) /\\ ( C =/= 0 -> 0 < B ) ) -> ( ( %s e. RR /\\ 0 <_ %s ) /\\ '
               '( ( ( abs ` C ) ^ 2 ) = ( %s x. B ) /\\ ( abs ` C ) <_ ( %s + B ) ) ) )') % (ANc, ANc, ANc, ANc)


def gen_anb():
    w = W('gf1anb', 'The Halasz weight ` a = abs ( c ) ^ 2 / b ` (with ` a = 0 ` for ` b = 0 ` ): ` 0 <_ a ` , ` abs ( c ) ^ 2 = a b ` , ` abs ( c ) <_ a + b ` .')
    X0, CONC = split_imp(S['gf1anb'])
    d = mk(w, X0)
    cn = proj(w, X0, 'C e. CC'); br = proj(w, X0, 'B e. RR'); b0 = proj(w, X0, '0 <_ B'); cb = proj(w, X0, '( C =/= 0 -> 0 < B )')
    CA2 = '( ( abs ` C ) ^ 2 )'
    acr = d('abscld', [cn], '( abs ` C ) e. RR')
    ca2r = d('resqcld', [acr], '%s e. RR' % CA2)
    Az = '( %s /\\ B = 0 )' % X0
    dz = mk(w, Az)
    bz = w.s([], 'simpr', '( %s -> B = 0 )' % Az)
    anz = dz('iftrued', [bz], '%s = 0' % ANc)
    notpos = dz('mtbird', [dz('ltnrd', [a1(w, Az, '0re', '0 e. RR')], '-. 0 < 0'), dz('breq2d', [bz], '( 0 < B <-> 0 < 0 )')], '-. 0 < B')
    c0 = dz('mpd', [notpos, dz('necon1bd', [lift(w, cb, Az)], '( -. 0 < B -> C = 0 )')], 'C = 0')
    ac0 = dz('eqtrd', [dz('fveq2d', [c0], '( abs ` C ) = ( abs ` 0 )'), a1(w, Az, 'abs0', '( abs ` 0 ) = 0')], '( abs ` C ) = 0')
    kz1 = dz('eqtrd', [dz('oveq1d', [ac0], '%s = ( 0 ^ 2 )' % CA2), a1(w, Az, 'sq0', '( 0 ^ 2 ) = 0')], '%s = 0' % CA2)
    kz2 = dz('eqtrd', [dz('oveq1d', [anz], '( %s x. B ) = ( 0 x. B )' % ANc), dz('mul02d', [dz('recnd', [lift(w, br, Az)], 'B e. CC')], '( 0 x. B ) = 0')], '( %s x. B ) = 0' % ANc)
    keyz = dz('eqtr4d', [kz1, kz2], '%s = ( %s x. B )' % (CA2, ANc))
    anrz = dz('eqeltrd', [anz, a1(w, Az, '0re', '0 e. RR')], '%s e. RR' % ANc)
    an0z = dz('breqtrrd', [dz('leidd', [a1(w, Az, '0re', '0 e. RR')], '0 <_ 0'), anz], '0 <_ %s' % ANc)
    bz_ = dz('3jca', [anrz, an0z, keyz], '( %s e. RR /\\ 0 <_ %s /\\ %s = ( %s x. B ) )' % (ANc, ANc, CA2, ANc))
    Anz = '( %s /\\ B =/= 0 )' % X0
    dnz = mk(w, Anz)
    bnz = w.s([], 'simpr', '( %s -> B =/= 0 )' % Anz)
    anq = dnz('syl', [bnz, w.inst('ifnefalse')], '%s = ( %s / B )' % (ANc, CA2))
    brz = lift(w, br, Anz)
    bpos = dnz('mpbird', [dnz('jca', [lift(w, b0, Anz), bnz], '( 0 <_ B /\\ B =/= 0 )'), dnz('syl2anc', [a1(w, Anz, '0re', '0 e. RR'), brz, w.inst('ltlen')], '( 0 < B <-> ( 0 <_ B /\\ B =/= 0 ) )')], '0 < B')
    qr = dnz('redivcld', [lift(w, ca2r, Anz), brz, bnz], '( %s / B ) e. RR' % CA2)
    q0 = dnz('divge0d', [lift(w, ca2r, Anz), dnz('elrpd', [brz, bpos], 'B e. RR+'), dnz('sqge0d', [lift(w, acr, Anz)], '0 <_ %s' % CA2)], '0 <_ ( %s / B )' % CA2)
    anrn = dnz('eqeltrd', [anq, qr], '%s e. RR' % ANc)
    an0n = dnz('breqtrrd', [q0, anq], '0 <_ %s' % ANc)
    keyn = dnz('eqtr2d', [dnz('oveq1d', [anq], '( %s x. B ) = ( ( %s / B ) x. B )' % (ANc, CA2)),
                          dnz('divcan1d', [dnz('recnd', [lift(w, ca2r, Anz)], '%s e. CC' % CA2), dnz('recnd', [brz], 'B e. CC'), bnz], '( ( %s / B ) x. B ) = %s' % (CA2, CA2))],
                  '%s = ( %s x. B )' % (CA2, ANc))
    bn_ = dnz('3jca', [anrn, an0n, keyn], '( %s e. RR /\\ 0 <_ %s /\\ %s = ( %s x. B ) )' % (ANc, ANc, CA2, ANc))
    al = d('pm2.61dane', [bz_, bn_], '( %s e. RR /\\ 0 <_ %s /\\ %s = ( %s x. B ) )' % (ANc, ANc, CA2, ANc))
    anr = d('simp1d', [al], '%s e. RR' % ANc); an0 = d('simp2d', [al], '0 <_ %s' % ANc); key = d('simp3d', [al], '%s = ( %s x. B )' % (CA2, ANc))
    abr = d('readdcld', [anr, br], '( %s + B ) e. RR' % ANc)
    ab0 = d('addge0d', [anr, br, an0, b0], '0 <_ ( %s + B )' % ANc)
    cl = Closure(w, X0, {ANc: anr, 'B': br})
    cl.atom(ANc)
    sq = lin.nlinarith(w, X0, [an0, b0], '( %s x. B ) <_ ( ( %s + B ) ^ 2 )' % (ANc, ANc), closure=cl)
    le = d('mpbird', [d('eqbrtrd', [key, sq], '%s <_ ( ( %s + B ) ^ 2 )' % (CA2, ANc)),
                      d('syl2anc', [d('jca', [acr, d('absge0d', [cn], '0 <_ ( abs ` C )')], '( ( abs ` C ) e. RR /\\ 0 <_ ( abs ` C ) )'), d('jca', [abr, ab0], '( ( %s + B ) e. RR /\\ 0 <_ ( %s + B ) )' % (ANc, ANc)),
                                    w.inst('le2sq')], '( ( abs ` C ) <_ ( %s + B ) <-> %s <_ ( ( %s + B ) ^ 2 ) )' % (ANc, CA2, ANc))], '( abs ` C ) <_ ( %s + B )' % ANc)
    fin = d('jca', [d('jca', [anr, an0], '( %s e. RR /\\ 0 <_ %s )' % (ANc, ANc)), d('jca', [key, le], '( %s = ( %s x. B ) /\\ ( abs ` C ) <_ ( %s + B ) )' % (CA2, ANc, ANc))], CONC)
    w.qed([fin], 'idi', S['gf1anb'])
    return run(w, only)


if __name__ == '__main__':
    gen_cvadd()
    gen_ser()
    gen_anb()
