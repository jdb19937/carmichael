"""Sortie GF1, section I: Halasz duality with majorants for series (gf1hal), from the finite
form gf1half by passing to the limit ( ~ climle ).
MM_DB=sorties/gf1.mm MM_ENGINE=mmatch python3 tools/gen/gf1_i.py [LABEL...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from gf1lib import *
sys.path.insert(0, os.path.dirname(__file__))
import gf1_h

only = sys.argv[1:]
c = lambda n: '( C ` %s )' % n
b = lambda n: '( B ` %s )' % n
x = lambda j, n: '( ( X ` %s ) ` %s )' % (j, n)
T = lambda j, v: '( %s x. %s )' % (c(v), x(j, v))
GRr = lambda j, k, v: '( ( %s x. %s ) x. ( * ` %s ) )' % (b(v), x(j, v), x(k, v))
PS = lambda j, m: 'sum_ n e. ( 1 ... %s ) %s' % (m, T(j, 'n'))
SA = lambda m: 'sum_ n e. ( 1 ... %s ) %s' % (m, AN('n'))
PG = lambda j, k, m: 'sum_ n e. ( 1 ... %s ) %s' % (m, GRr(j, k, 'n'))
LHS = lambda m: '( sum_ j e. J ( abs ` %s ) ^ 2 )' % PS('j', m)
QS = lambda m: 'sum_ j e. J sum_ k e. J ( abs ` %s )' % PG('j', 'k', m)
RHS = lambda m: '( %s x. %s )' % (SA(m), QS(m))
FJ = 'sum_ n e. NN %s' % T('j', 'n')
SAI = 'sum_ n e. NN %s' % AN('n')
GJK = 'sum_ n e. NN %s' % GRr('j', 'k', 'n')
NU = 'NN = ( ZZ>= ` 1 )'


def gen_hal():
    w = W('gf1hal', 'Blueprint Lemma 5.1, Halasz duality with majorants: ` ( sum_j abs F_j ) ^ 2 <_ ( sum_n abs c_n ^ 2 / b_n ) sum_j sum_k abs sum_n b_n x_j ( n ) * x_k ( n ) ` for coefficients ` c ` , a majorant ` b >_ 0 ` ( ` c_n =/= 0 -> b_n > 0 ` ) and vectors ` abs x_j ( n ) <_ 1 ` (Lean ` halasz_duality ` , generic; ~ gf1half at every truncation, ~ climle ).')
    h1, h2, h3, h4, h5 = ehyps(w, 'gf1hal')
    A = 'ph'
    d = mk(w, A)
    nu = w.s([], 'nnuz', NU)
    one = a1(w, A, '1z', '1 e. ZZ')
    # ---- n-level facts
    An = '( ph /\\ n e. NN )'
    dn = mk(w, An)
    cn = dn('simp1d', [h3], '%s e. CC' % c('n'))
    bpair = dn('simp2d', [h3], '( %s e. RR /\\ 0 <_ %s )' % (b('n'), b('n')))
    br = dn('simpld', [bpair], '%s e. RR' % b('n')); b0 = dn('simprd', [bpair], '0 <_ %s' % b('n'))
    anb = dn('syl', [h3, w.inst('gf1anb')], tsub(split_imp(S['gf1anb'])[1].replace('if ( B = 0 , 0 , ( ( ( abs ` C ) ^ 2 ) / B ) )', 'ANX'), {'C': c('n'), 'B': b('n')}).replace('ANX', AN('n')))
    anr = dn('simplld' if False else 'simpld', [dn('simpld', [anb], '( %s e. RR /\\ 0 <_ %s )' % (AN('n'), AN('n')))], '%s e. RR' % AN('n'))
    an0 = dn('simprd', [dn('simpld', [anb], '( %s e. RR /\\ 0 <_ %s )' % (AN('n'), AN('n')))], '0 <_ %s' % AN('n'))
    cle = dn('simprd', [dn('simprd', [anb], '( ( ( abs ` %s ) ^ 2 ) = ( %s x. %s ) /\\ ( abs ` %s ) <_ ( %s + %s ) )' % (c('n'), AN('n'), b('n'), c('n'), AN('n'), b('n')))],
             '( abs ` %s ) <_ ( %s + %s )' % (c('n'), AN('n'), b('n')))
    Ajn = '( ph /\\ ( j e. J /\\ n e. NN ) )'
    xx = w.s([h2], 'idi', '') if False else None
    xc2 = D(w, Ajn, 'simpld', [h2], '%s e. CC' % x('j', 'n')); x1 = D(w, Ajn, 'simprd', [h2], '( abs ` %s ) <_ 1' % x('j', 'n'))
    Aj = '( ph /\\ j e. J )'
    dj = mk(w, Aj)
    Ajn_ = '( %s /\\ n e. NN )' % Aj
    xc = w.s([xc2], 'anassrs', '( %s -> %s e. CC )' % (Ajn_, x('j', 'n')))
    xa1 = w.s([x1], 'anassrs', '( %s -> ( abs ` %s ) <_ 1 )' % (Ajn_, x('j', 'n')))
    def toAn(ctx):
        return D(w, ctx, 'jca', [w.s([], 'simpll', '( %s -> ph )' % ctx) if ctx.count('/\\') >= 2 else w.s([], 'simpl', '( %s -> ph )' % ctx), w.s([], 'simpr', '( %s -> n e. NN )' % ctx)], An)
    def under(ctx, st):
        from cl import formula_of
        src, concl = split_imp(formula_of(w, st))
        return w.s([proj(w, ctx, src), st], 'syl', '( %s -> %s )' % (ctx, concl))
    # ---- (b) the finite inequality at every truncation ( 1 ... i )
    Ai = '( ph /\\ i e. NN )'
    di = mk(w, Ai)
    I_ = '( 1 ... i )'
    fin1 = di('jca', [lift(w, h1, Ai), di('fzfid', [], '%s e. Fin' % I_)], '( J e. Fin /\\ %s e. Fin )' % I_)
    Aijn = '( %s /\\ ( j e. J /\\ n e. %s ) )' % (Ai, I_)
    nnI = D(w, Aijn, 'syl', [D(w, Aijn, 'simprd', [w.s([], 'simpr', '( %s -> ( j e. J /\\ n e. %s ) )' % (Aijn, I_))], 'n e. %s' % I_), w.inst('elfznn')], 'n e. NN')
    xI = w.s([D(w, Aijn, 'jca', [w.s([], 'simpll', '( %s -> ph )' % Aijn), D(w, Aijn, 'jca', [D(w, Aijn, 'simprd' if False else 'simpld', [w.s([], 'simpr', '( %s -> ( j e. J /\\ n e. %s ) )' % (Aijn, I_))], 'j e. J'), nnI], '( j e. J /\\ n e. NN )')],
                        '( ph /\\ ( j e. J /\\ n e. NN ) )'), xc2], 'syl', '( %s -> %s e. CC )' % (Aijn, x('j', 'n')))
    Ain = '( %s /\\ n e. %s )' % (Ai, I_)
    nnI2 = D(w, Ain, 'syl', [w.s([], 'simpr', '( %s -> n e. %s )' % (Ain, I_)), w.inst('elfznn')], 'n e. NN')
    h3I = w.s([D(w, Ain, 'jca', [w.s([], 'simpll', '( %s -> ph )' % Ain), nnI2], An), h3], 'syl', '( %s -> %s )' % (Ain, split_imp(S['gf1hal.3'])[1]))
    half = w.s([fin1, xI, h3I], 'gf1half', '( %s -> %s <_ %s )' % (Ai, LHS('i'), RHS('i')))
    # ---- (c) convergence of the series
    AF = '( p e. NN |-> %s )' % AN('p')
    anpn = w.s([w.s([], 'fveq2', '( n = p -> ( B ` n ) = ( B ` p ) )'), w.s([], 'fveq2', '( n = p -> ( C ` n ) = ( C ` p ) )')], 'idi', '') if False else None
    e_b = w.s([], 'fveq2', '( n = p -> ( B ` n ) = ( B ` p ) )')
    e_c = w.s([], 'fveq2', '( n = p -> ( C ` n ) = ( C ` p ) )')
    e_1 = w.s([e_b], 'eqeq1d', '( n = p -> ( ( B ` n ) = 0 <-> ( B ` p ) = 0 ) )')
    e_2 = w.s([w.s([w.s([e_c], 'fveq2d', '( n = p -> ( abs ` ( C ` n ) ) = ( abs ` ( C ` p ) ) )')], 'oveq1d', '( n = p -> ( ( abs ` ( C ` n ) ) ^ 2 ) = ( ( abs ` ( C ` p ) ) ^ 2 ) )'), e_b], 'oveq12d',
              '( n = p -> ( ( ( abs ` ( C ` n ) ) ^ 2 ) / ( B ` n ) ) = ( ( ( abs ` ( C ` p ) ) ^ 2 ) / ( B ` p ) ) )')
    e_an = w.s([e_1, e_2], 'ifbieq2d', '( n = p -> %s = %s )' % (AN('n'), AN('p')))
    cbA = w.s([e_an], 'cbvmptv', '( n e. NN |-> %s ) = %s' % (AN('n'), AF))
    h4p = d('eqeltrd', [w.s([w.s([w.s([cbA, w.inst('seqeq3')], 'ax-mp', 'seq 1 ( + , ( n e. NN |-> %s ) ) = seq 1 ( + , %s )' % (AN('n'), AF))], 'eqcomi',
                             'seq 1 ( + , %s ) = seq 1 ( + , ( n e. NN |-> %s ) )' % (AF, AN('n')))], 'a1i', '( ph -> seq 1 ( + , %s ) = seq 1 ( + , ( n e. NN |-> %s ) ) )' % (AF, AN('n'))), h4],
            'seq 1 ( + , %s ) e. dom ~~>' % AF)
    def fvAF(ctx, v, vin, vr):
        """( ctx -> ( AF ` v ) = AN(v) )"""
        sb = w.s([w.s([w.s([], 'fveq2', '( p = %s -> ( B ` p ) = ( B ` %s ) )' % (v, v))], 'eqeq1d', '( p = %s -> ( ( B ` p ) = 0 <-> ( B ` %s ) = 0 ) )' % (v, v)),
                  w.s([w.s([w.s([w.s([], 'fveq2', '( p = %s -> ( C ` p ) = ( C ` %s ) )' % (v, v))], 'fveq2d', '( p = %s -> ( abs ` ( C ` p ) ) = ( abs ` ( C ` %s ) ) )' % (v, v))], 'oveq1d',
                             '( p = %s -> ( ( abs ` ( C ` p ) ) ^ 2 ) = ( ( abs ` ( C ` %s ) ) ^ 2 ) )' % (v, v)), w.s([], 'fveq2', '( p = %s -> ( B ` p ) = ( B ` %s ) )' % (v, v))], 'oveq12d',
                      '( p = %s -> ( ( ( abs ` ( C ` p ) ) ^ 2 ) / ( B ` p ) ) = ( ( ( abs ` ( C ` %s ) ) ^ 2 ) / ( B ` %s ) ) )' % (v, v, v))], 'ifbieq2d', '( p = %s -> %s = %s )' % (v, AN('p'), AN(v)))
        return D(w, ctx, 'fvmptd', [w.s([], 'eqidd', '( %s -> %s = %s )' % (ctx, AF, AF)), w.s([sb], 'adantl', '( ( %s /\\ p = %s ) -> %s = %s )' % (ctx, v, AN('p'), AN(v))), vin,
                                    D(w, ctx, 'recnd', [vr], '%s e. CC' % AN(v))], '( %s ` %s ) = %s' % (AF, v, AN(v)))
    nin = w.s([], 'simpr', '( %s -> n e. NN )' % An)
    afn = fvAF(An, 'n', nin, anr)
    afc = dn('eqeltrd', [afn, dn('recnd', [anr], '%s e. CC' % AN('n'))], '( %s ` n ) e. CC' % AF)
    UU = '( q e. NN |-> ( ( %s ` q ) + ( B ` q ) ) )' % AF
    uuc = d('gf1cvadd', [afc, dn('recnd', [br], '%s e. CC' % b('n')), h4p, h5], 'seq 1 ( + , %s ) e. dom ~~>' % UU)
    uv = dn('fvmptd', [w.s([], 'eqidd', '( %s -> %s = %s )' % (An, UU, UU)),
                       w.s([w.s([w.s([], 'fveq2', '( q = n -> ( %s ` q ) = ( %s ` n ) )' % (AF, AF)), w.s([], 'fveq2', '( q = n -> ( B ` q ) = ( B ` n ) )')], 'oveq12d',
                                '( q = n -> ( ( %s ` q ) + ( B ` q ) ) = ( ( %s ` n ) + ( B ` n ) ) )' % (AF, AF))], 'adantl', '( ( %s /\\ q = n ) -> ( ( %s ` q ) + ( B ` q ) ) = ( ( %s ` n ) + ( B ` n ) ) )' % (An, AF, AF)),
                       nin, dn('addcld', [afc, dn('recnd', [br], '%s e. CC' % b('n'))], '( ( %s ` n ) + ( B ` n ) ) e. CC' % AF)], '( %s ` n ) = ( ( %s ` n ) + ( B ` n ) )' % (UU, AF))
    uv2 = dn('eqtrd', [uv, dn('oveq1d', [afn], '( ( %s ` n ) + ( B ` n ) ) = ( %s + %s )' % (AF, AN('n'), b('n')))], '( %s ` n ) = ( %s + %s )' % (UU, AN('n'), b('n')))
    uur = dn('eqeltrd', [uv2, dn('readdcld', [anr, br], '( %s + %s ) e. RR' % (AN('n'), b('n')))], '( %s ` n ) e. RR' % UU)
    # the j-series
    TJ = '( p e. NN |-> %s )' % T('j', 'p')
    dAjn = mk(w, Ajn_)
    nj = w.s([], 'simpr', '( %s -> n e. NN )' % Ajn_)
    cnj = under(Ajn_, cn)
    tval = dAjn('fvmptd', [w.s([], 'eqidd', '( %s -> %s = %s )' % (Ajn_, TJ, TJ)),
                           w.s([w.s([w.s([], 'fveq2', '( p = n -> ( C ` p ) = ( C ` n ) )'), w.s([], 'fveq2', '( p = n -> ( ( X ` j ) ` p ) = ( ( X ` j ) ` n ) )')], 'oveq12d',
                                    '( p = n -> %s = %s )' % (T('j', 'p'), T('j', 'n')))], 'adantl', '( ( %s /\\ p = n ) -> %s = %s )' % (Ajn_, T('j', 'p'), T('j', 'n'))),
                           nj, dAjn('mulcld', [cnj, xc], '%s e. CC' % T('j', 'n'))], '( %s ` n ) = %s' % (TJ, T('j', 'n')))
    tjc = dAjn('eqeltrd', [tval, dAjn('mulcld', [cnj, xc], '%s e. CC' % T('j', 'n'))], '( %s ` n ) e. CC' % TJ)
    # |T| <_ 1 x. UU
    acn = dAjn('abscld', [cnj], '( abs ` %s ) e. RR' % c('n'))
    axr = dAjn('abscld', [xc], '( abs ` %s ) e. RR' % x('j', 'n'))
    tab = dAjn('eqtrd', [dAjn('fveq2d', [tval], '( abs ` ( %s ` n ) ) = ( abs ` %s )' % (TJ, T('j', 'n'))), dAjn('absmuld', [cnj, xc], '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (T('j', 'n'), c('n'), x('j', 'n')))],
                 '( abs ` ( %s ` n ) ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (TJ, c('n'), x('j', 'n')))
    m1 = dAjn('lemul12ad', [acn, under(Ajn_, dn('readdcld', [anr, br], '( %s + %s ) e. RR' % (AN('n'), b('n')))), axr, a1(w, Ajn_, '1re', '1 e. RR'),
                            dAjn('absge0d', [cnj], '0 <_ ( abs ` %s )' % c('n')), under(Ajn_, cle), dAjn('absge0d', [xc], '0 <_ ( abs ` %s )' % x('j', 'n')), xa1],
              '( ( abs ` %s ) x. ( abs ` %s ) ) <_ ( ( %s + %s ) x. 1 )' % (c('n'), x('j', 'n'), AN('n'), b('n')))
    abc = dAjn('recnd', [under(Ajn_, dn('readdcld', [anr, br], '( %s + %s ) e. RR' % (AN('n'), b('n'))))], '( %s + %s ) e. CC' % (AN('n'), b('n')))
    m2 = dAjn('eqtr4d', [dAjn('mulridd', [abc], '( ( %s + %s ) x. 1 ) = ( %s + %s )' % (AN('n'), b('n'), AN('n'), b('n'))),
                         dAjn('eqtrd', [dAjn('mullidd', [dAjn('recnd', [under(Ajn_, uur)], '( %s ` n ) e. CC' % UU)], '( 1 x. ( %s ` n ) ) = ( %s ` n )' % (UU, UU)), under(Ajn_, uv2)],
                              '( 1 x. ( %s ` n ) ) = ( %s + %s )' % (UU, AN('n'), b('n')))], '( ( %s + %s ) x. 1 ) = ( 1 x. ( %s ` n ) )' % (AN('n'), b('n'), UU))
    tb = chain(w, Ajn_, ['( abs ` ( %s ` n ) )' % TJ, '( ( abs ` %s ) x. ( abs ` %s ) )' % (c('n'), x('j', 'n')), '( ( %s + %s ) x. 1 )' % (AN('n'), b('n')), '( 1 x. ( %s ` n ) )' % UU],
               [tab, m1, m2], ['=', '<_', '='])
    Aju = '( %s /\\ n e. ( ZZ>= ` 1 ) )' % Aj
    tbu = w.s([D(w, Aju, 'jca', [w.s([], 'simpl', '( %s -> %s )' % (Aju, Aj)), D(w, Aju, 'eleqtrrdi', [w.s([], 'simpr', '( %s -> n e. ( ZZ>= ` 1 ) )' % Aju), nu], 'n e. NN')], Ajn_), tb], 'syl',
              '( %s -> ( abs ` ( %s ` n ) ) <_ ( 1 x. ( %s ` n ) ) )' % (Aju, TJ, UU))
    tcv = dj('cvgcmpce', [nu, a1(w, Aj, '1nn', '1 e. NN'), under(Ajn_, uur), tjc, lift(w, uuc, Aj), a1(w, Aj, '1re', '1 e. RR'), tbu], 'seq 1 ( + , %s ) e. dom ~~>' % TJ)
    # ---- generic: from gf1ser for a function G to the class form of partial sums and limit
    def partial(ctx, G, body, gval, gc, gcv, Actxn):
        """gval ( Actxn -> ( G ` n ) = body ), Actxn = ( ctx /\\ n e. NN ); returns ( ctx -> ( m e. NN |-> sum_ n e. ( 1 ... m ) body ) ~~> sum_ n e. NN body )"""
        sr = D(w, ctx, 'gf1ser', [gc, gcv], '( m e. NN |-> sum_ n e. ( 1 ... m ) ( %s ` n ) ) ~~> sum_ n e. NN ( %s ` n )' % (G, G))
        lim = D(w, ctx, 'sumeq2dv', [gval], 'sum_ n e. NN ( %s ` n ) = sum_ n e. NN %s' % (G, body))
        Cm = '( %s /\\ m e. NN )' % ctx
        Cmn = '( %s /\\ n e. ( 1 ... m ) )' % Cm
        nnm = D(w, Cmn, 'syl', [w.s([], 'simpr', '( %s -> n e. ( 1 ... m ) )' % Cmn), w.inst('elfznn')], 'n e. NN')
        gv2 = w.s([D(w, Cmn, 'jca', [w.s([], 'simpll', '( %s -> %s )' % (Cmn, ctx)), nnm], Actxn), gval], 'syl', '( %s -> ( %s ` n ) = %s )' % (Cmn, G, body))
        ps = D(w, Cm, 'sumeq2dv', [gv2], 'sum_ n e. ( 1 ... m ) ( %s ` n ) = sum_ n e. ( 1 ... m ) %s' % (G, body))
        mp = D(w, ctx, 'mpteq2dva', [ps], '( m e. NN |-> sum_ n e. ( 1 ... m ) ( %s ` n ) ) = ( m e. NN |-> sum_ n e. ( 1 ... m ) %s )' % (G, body))
        res = D(w, ctx, 'breq12d', [mp, lim], '( ( m e. NN |-> sum_ n e. ( 1 ... m ) ( %s ` n ) ) ~~> sum_ n e. NN ( %s ` n ) <-> ( m e. NN |-> sum_ n e. ( 1 ... m ) %s ) ~~> sum_ n e. NN %s )' % (G, G, body, body))
        return D(w, ctx, 'mpbid', [sr, res], '( m e. NN |-> sum_ n e. ( 1 ... m ) %s ) ~~> sum_ n e. NN %s' % (body, body))
    def mval(ctx, body_m, body_i, sub_step, bc):
        """( ( ctx /\\ i e. NN ) -> ( ( m e. NN |-> body_m ) ` i ) = body_i ); sub_step ( m = i -> body_m = body_i ); bc ( ( ctx /\\ i e. NN ) -> body_i e. CC )"""
        Ci = '( %s /\\ i e. NN )' % ctx
        MPt = '( m e. NN |-> %s )' % body_m
        return D(w, Ci, 'fvmptd', [w.s([], 'eqidd', '( %s -> %s = %s )' % (Ci, MPt, MPt)), w.s([sub_step], 'adantl', '( ( %s /\\ m = i ) -> %s = %s )' % (Ci, body_m, body_i)),
                                   w.s([], 'simpr', '( %s -> i e. NN )' % Ci), bc], '( %s ` i ) = %s' % (MPt, body_i))
    def sumsub(body):
        """( m = i -> sum_ n e. ( 1 ... m ) body = sum_ n e. ( 1 ... i ) body )"""
        return w.s([w.s([], 'oveq2', '( m = i -> ( 1 ... m ) = ( 1 ... i ) )')], 'sumeq1d', '( m = i -> sum_ n e. ( 1 ... m ) %s = sum_ n e. ( 1 ... i ) %s )' % (body, body))
    # ---- (d)(e) the j-series: partial sums converge; absolute values converge
    Tn = T('j', 'n')
    pj = partial(Aj, TJ, Tn, tval, tjc, tcv, Ajn_)
    Aji = '( %s /\\ i e. NN )' % Aj
    dji = mk(w, Aji)
    Ajin = '( %s /\\ n e. ( 1 ... i ) )' % Aji
    nnji = D(w, Ajin, 'syl', [w.s([], 'simpr', '( %s -> n e. ( 1 ... i ) )' % Ajin), w.inst('elfznn')], 'n e. NN')
    tcji = w.s([D(w, Ajin, 'jca', [w.s([], 'simpll', '( %s -> %s )' % (Ajin, Aj)), nnji], Ajn_), dAjn('mulcld', [cnj, xc], '%s e. CC' % Tn)], 'syl', '( %s -> %s e. CC )' % (Ajin, Tn))
    psc = dji('fsumcl', [dji('fzfid', [], '( 1 ... i ) e. Fin'), tcji], '%s e. CC' % PS('j', 'i'))
    LSJ = '( m e. NN |-> %s )' % PS('j', 'm')
    lsv = mval(Aj, PS('j', 'm'), PS('j', 'i'), sumsub(Tn), psc)
    ABJ = '( m e. NN |-> ( abs ` %s ) )' % PS('j', 'm')
    absv = mval(Aj, '( abs ` %s )' % PS('j', 'm'), '( abs ` %s )' % PS('j', 'i'), w.s([sumsub(Tn)], 'fveq2d', '( m = i -> ( abs ` %s ) = ( abs ` %s ) )' % (PS('j', 'm'), PS('j', 'i'))),
                dji('abscld' if False else 'recnd', [dji('abscld', [psc], '( abs ` %s ) e. RR' % PS('j', 'i'))], '( abs ` %s ) e. CC' % PS('j', 'i')))
    ca = dj('climabs', [nu, pj, a1(w, Aj, 'mptex', '%s e. _V' % ABJ, [w.s([], 'nnex', 'NN e. _V')]), lift(w, one, Aj), dji('eqeltrd', [lsv, psc], '( %s ` i ) e. CC' % LSJ),
                        dji('eqtr4d', [absv, dji('fveq2d', [lsv], '( abs ` ( %s ` i ) ) = ( abs ` %s )' % (LSJ, PS('j', 'i')))], '( %s ` i ) = ( abs ` ( %s ` i ) )' % (ABJ, LSJ))],
            '%s ~~> ( abs ` %s )' % (ABJ, FJ))
    # ---- (f) sum over j, (g) square
    HJ = '( m e. NN |-> sum_ j e. J ( abs ` %s ) )' % PS('j', 'm')
    dI = mk(w, Ai)
    Aij = '( %s /\\ j e. J )' % Ai
    toAji = D(w, Aij, 'jca', [D(w, Aij, 'jca', [w.s([], 'simpll', '( %s -> ph )' % Aij), w.s([], 'simpr', '( %s -> j e. J )' % Aij)], Aj), w.s([], 'simplr', '( %s -> i e. NN )' % Aij)], Aji)
    absr_ij = w.s([toAji, dji('abscld', [psc], '( abs ` %s ) e. RR' % PS('j', 'i'))], 'syl', '( %s -> ( abs ` %s ) e. RR )' % (Aij, PS('j', 'i')))
    sumr_i = dI('fsumrecl', [lift(w, h1, Ai), absr_ij], 'sum_ j e. J ( abs ` %s ) e. RR' % PS('j', 'i'))
    hjv = mval('ph', 'sum_ j e. J ( abs ` %s )' % PS('j', 'm'), 'sum_ j e. J ( abs ` %s )' % PS('j', 'i'),
               w.s([w.s([sumsub(Tn)], 'fveq2d', '( m = i -> ( abs ` %s ) = ( abs ` %s ) )' % (PS('j', 'm'), PS('j', 'i')))], 'sumeq2sdv', '( m = i -> sum_ j e. J ( abs ` %s ) = sum_ j e. J ( abs ` %s ) )' % (PS('j', 'm'), PS('j', 'i'))),
               dI('recnd', [sumr_i], 'sum_ j e. J ( abs ` %s ) e. CC' % PS('j', 'i')))
    Aji2 = '( ph /\\ ( j e. J /\\ i e. NN ) )'
    absv2 = w.s([absv], 'anasss', '( %s -> ( %s ` i ) = ( abs ` %s ) )' % (Aji2, ABJ, PS('j', 'i')))
    abc2 = w.s([dji('eqeltrd', [absv, dji('recnd', [dji('abscld', [psc], '( abs ` %s ) e. RR' % PS('j', 'i'))], '( abs ` %s ) e. CC' % PS('j', 'i'))], '( %s ` i ) e. CC' % ABJ)], 'anasss',
               '( %s -> ( %s ` i ) e. CC )' % (Aji2, ABJ))
    hsum = dI('eqtr4d', [hjv, dI('sumeq2dv', [w.s([toAji, absv], 'syl', '( %s -> ( %s ` i ) = ( abs ` %s ) )' % (Aij, ABJ, PS('j', 'i')))],
                                 'sum_ j e. J ( %s ` i ) = sum_ j e. J ( abs ` %s )' % (ABJ, PS('j', 'i')))], '( %s ` i ) = sum_ j e. J ( %s ` i )' % (HJ, ABJ))
    ch = d('climfsum', [nu, one, h1, ca, a1(w, A, 'mptex', '%s e. _V' % HJ, [w.s([], 'nnex', 'NN e. _V')]), abc2, hsum], '%s ~~> sum_ j e. J ( abs ` %s )' % (HJ, FJ))
    LF = '( m e. NN |-> %s )' % LHS('m')
    SJI = 'sum_ j e. J ( abs ` %s )' % PS('j', 'i')
    lfv = mval('ph', LHS('m'), LHS('i'), w.s([w.s([w.s([sumsub(Tn)], 'fveq2d', '( m = i -> ( abs ` %s ) = ( abs ` %s ) )' % (PS('j', 'm'), PS('j', 'i')))], 'sumeq2sdv',
                                                   '( m = i -> sum_ j e. J ( abs ` %s ) = %s )' % (PS('j', 'm'), SJI))], 'oveq1d', '( m = i -> %s = %s )' % (LHS('m'), LHS('i'))),
               dI('recnd', [dI('resqcld', [sumr_i], '%s e. RR' % LHS('i'))], '%s e. CC' % LHS('i')))
    hjc = dI('eqeltrd', [hjv, dI('recnd', [sumr_i], '%s e. CC' % SJI)], '( %s ` i ) e. CC' % HJ)
    lfm = dI('eqtrd', [lfv, dI('eqtr4d', [dI('sqvald', [dI('recnd', [sumr_i], '%s e. CC' % SJI)], '%s = ( %s x. %s )' % (LHS('i'), SJI, SJI)),
                                          dI('oveq12d', [hjv, hjv], '( ( %s ` i ) x. ( %s ` i ) ) = ( %s x. %s )' % (HJ, HJ, SJI, SJI))], '%s = ( ( %s ` i ) x. ( %s ` i ) )' % (LHS('i'), HJ, HJ))],
              '( %s ` i ) = ( ( %s ` i ) x. ( %s ` i ) )' % (LF, HJ, HJ))
    SFJ = 'sum_ j e. J ( abs ` %s )' % FJ
    cl = d('climmul', [nu, one, ch, a1(w, A, 'mptex', '%s e. _V' % LF, [w.s([], 'nnex', 'NN e. _V')]), ch, hjc, hjc, lfm], '%s ~~> ( %s x. %s )' % (LF, SFJ, SFJ))
    # ---- (h) the right side
    pa = partial('ph', AF, AN('n'), afn, afc, h4p, An)
    SAm = '( m e. NN |-> %s )' % SA('m')
    Ain2 = '( %s /\\ n e. ( 1 ... i ) )' % Ai
    nni2 = D(w, Ain2, 'syl', [w.s([], 'simpr', '( %s -> n e. ( 1 ... i ) )' % Ain2), w.inst('elfznn')], 'n e. NN')
    anci = w.s([D(w, Ain2, 'jca', [w.s([], 'simpll', '( %s -> ph )' % Ain2), nni2], An), dn('recnd', [anr], '%s e. CC' % AN('n'))], 'syl', '( %s -> %s e. CC )' % (Ain2, AN('n')))
    anri = w.s([D(w, Ain2, 'jca', [w.s([], 'simpll', '( %s -> ph )' % Ain2), nni2], An), anr], 'syl', '( %s -> %s e. RR )' % (Ain2, AN('n')))
    sar_i = dI('fsumrecl', [dI('fzfid', [], '( 1 ... i ) e. Fin'), anri], '%s e. RR' % SA('i'))
    sav = mval('ph', SA('m'), SA('i'), sumsub(AN('n')), dI('recnd', [sar_i], '%s e. CC' % SA('i')))
    # x ( k , n ) facts
    Pj = '( %s e. CC /\\ ( abs ` %s ) <_ 1 )' % (x('j', 'n'), x('j', 'n'))
    Pk = '( %s e. CC /\\ ( abs ` %s ) <_ 1 )' % (x('k', 'n'), x('k', 'n'))
    ralj = dn('ralrimiva', [under('( %s /\\ j e. J )' % An, h2)], 'A. j e. J %s' % Pj)
    exk = w.s([], 'fveq2', '( j = k -> ( X ` j ) = ( X ` k ) )')
    exn = w.s([exk], 'fveq1d', '( j = k -> %s = %s )' % (x('j', 'n'), x('k', 'n')))
    pjk = w.s([w.s([exn], 'eleq1d', '( j = k -> ( %s e. CC <-> %s e. CC ) )' % (x('j', 'n'), x('k', 'n'))),
               w.s([w.s([exn], 'fveq2d', '( j = k -> ( abs ` %s ) = ( abs ` %s ) )' % (x('j', 'n'), x('k', 'n')))], 'breq1d', '( j = k -> ( ( abs ` %s ) <_ 1 <-> ( abs ` %s ) <_ 1 ) )' % (x('j', 'n'), x('k', 'n')))],
              'anbi12d', '( j = k -> ( %s <-> %s ) )' % (Pj, Pk))
    rsk = w.s([pjk], 'rspcv', '( k e. J -> ( A. j e. J %s -> %s ) )' % (Pj, Pk))
    Ajk = '( %s /\\ k e. J )' % Aj
    Ajkn = '( %s /\\ n e. NN )' % Ajk
    dq = mk(w, Ajkn)
    pk = dq('sylc', [w.s([], 'simplr', '( %s -> k e. J )' % Ajkn), under(Ajkn, ralj), rsk], Pk)
    xkc = dq('simpld', [pk], '%s e. CC' % x('k', 'n')); xk1 = dq('simprd', [pk], '( abs ` %s ) <_ 1' % x('k', 'n'))
    xjc = under(Ajkn, xc); xj1 = under(Ajkn, xa1)
    bq = under(Ajkn, br); bq0 = under(Ajkn, b0)
    GRn = GRr('j', 'k', 'n')
    grc = dq('mulcld', [dq('mulcld', [dq('recnd', [bq], '%s e. CC' % b('n')), xjc], '( %s x. %s ) e. CC' % (b('n'), x('j', 'n'))), dq('cjcld', [xkc], '( * ` %s ) e. CC' % x('k', 'n'))], '%s e. CC' % GRn)
    WJK = '( p e. NN |-> %s )' % GRr('j', 'k', 'p')
    wv = dq('fvmptd', [w.s([], 'eqidd', '( %s -> %s = %s )' % (Ajkn, WJK, WJK)),
                       w.s([w.s([w.s([w.s([], 'fveq2', '( p = n -> ( B ` p ) = ( B ` n ) )'), w.s([], 'fveq2', '( p = n -> ( ( X ` j ) ` p ) = ( ( X ` j ) ` n ) )')], 'oveq12d',
                                     '( p = n -> ( ( B ` p ) x. ( ( X ` j ) ` p ) ) = ( ( B ` n ) x. ( ( X ` j ) ` n ) ) )'),
                                 w.s([w.s([], 'fveq2', '( p = n -> ( ( X ` k ) ` p ) = ( ( X ` k ) ` n ) )')], 'fveq2d', '( p = n -> ( * ` ( ( X ` k ) ` p ) ) = ( * ` ( ( X ` k ) ` n ) ) )')], 'oveq12d',
                                '( p = n -> %s = %s )' % (GRr('j', 'k', 'p'), GRn))], 'adantl', '( ( %s /\\ p = n ) -> %s = %s )' % (Ajkn, GRr('j', 'k', 'p'), GRn)),
                       w.s([], 'simpr', '( %s -> n e. NN )' % Ajkn), grc], '( %s ` n ) = %s' % (WJK, GRn))
    wc = dq('eqeltrd', [wv, grc], '( %s ` n ) e. CC' % WJK)
    axj = dq('abscld', [xjc], '( abs ` %s ) e. RR' % x('j', 'n')); axk = dq('abscld', [xkc], '( abs ` %s ) e. RR' % x('k', 'n'))
    aw = chain(w, Ajkn, ['( abs ` ( %s ` n ) )' % WJK, '( abs ` %s )' % GRn, '( ( abs ` ( %s x. %s ) ) x. ( abs ` ( * ` %s ) ) )' % (b('n'), x('j', 'n'), x('k', 'n')),
                         '( ( %s x. ( abs ` %s ) ) x. ( abs ` %s ) )' % (b('n'), x('j', 'n'), x('k', 'n')), '( %s x. ( ( abs ` %s ) x. ( abs ` %s ) ) )' % (b('n'), x('j', 'n'), x('k', 'n'))],
               [dq('fveq2d', [wv], '( abs ` ( %s ` n ) ) = ( abs ` %s )' % (WJK, GRn)),
                dq('absmuld', [dq('mulcld', [dq('recnd', [bq], '%s e. CC' % b('n')), xjc], '( %s x. %s ) e. CC' % (b('n'), x('j', 'n'))), dq('cjcld', [xkc], '( * ` %s ) e. CC' % x('k', 'n'))],
                   '( abs ` %s ) = ( ( abs ` ( %s x. %s ) ) x. ( abs ` ( * ` %s ) ) )' % (GRn, b('n'), x('j', 'n'), x('k', 'n'))),
                dq('oveq12d', [dq('eqtrd', [dq('absmuld', [dq('recnd', [bq], '%s e. CC' % b('n')), xjc], '( abs ` ( %s x. %s ) ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (b('n'), x('j', 'n'), b('n'), x('j', 'n'))),
                                            dq('oveq1d', [dq('absidd', [bq, bq0], '( abs ` %s ) = %s' % (b('n'), b('n')))], '( ( abs ` %s ) x. ( abs ` %s ) ) = ( %s x. ( abs ` %s ) )' % (b('n'), x('j', 'n'), b('n'), x('j', 'n')))],
                                   '( abs ` ( %s x. %s ) ) = ( %s x. ( abs ` %s ) )' % (b('n'), x('j', 'n'), b('n'), x('j', 'n'))), dq('abscjd', [xkc], '( abs ` ( * ` %s ) ) = ( abs ` %s )' % (x('k', 'n'), x('k', 'n')))],
                   '( ( abs ` ( %s x. %s ) ) x. ( abs ` ( * ` %s ) ) ) = ( ( %s x. ( abs ` %s ) ) x. ( abs ` %s ) )' % (b('n'), x('j', 'n'), x('k', 'n'), b('n'), x('j', 'n'), x('k', 'n'))),
                dq('mulassd', [dq('recnd', [bq], '%s e. CC' % b('n')), dq('recnd', [axj], '( abs ` %s ) e. CC' % x('j', 'n')), dq('recnd', [axk], '( abs ` %s ) e. CC' % x('k', 'n'))],
                   '( ( %s x. ( abs ` %s ) ) x. ( abs ` %s ) ) = ( %s x. ( ( abs ` %s ) x. ( abs ` %s ) ) )' % (b('n'), x('j', 'n'), x('k', 'n'), b('n'), x('j', 'n'), x('k', 'n')))])
    uv1 = dq('lemul12ad', [axj, a1(w, Ajkn, '1re', '1 e. RR'), axk, a1(w, Ajkn, '1re', '1 e. RR'), dq('absge0d', [xjc], '0 <_ ( abs ` %s )' % x('j', 'n')), xj1, dq('absge0d', [xkc], '0 <_ ( abs ` %s )' % x('k', 'n')), xk1],
              '( ( abs ` %s ) x. ( abs ` %s ) ) <_ ( 1 x. 1 )' % (x('j', 'n'), x('k', 'n')))
    uv2_ = dq('breqtrd', [uv1, a1(w, Ajkn, '1t1e1', '( 1 x. 1 ) = 1')], '( ( abs ` %s ) x. ( abs ` %s ) ) <_ 1' % (x('j', 'n'), x('k', 'n')))
    bu = dq('lemul2ad', [dq('remulcld', [axj, axk], '( ( abs ` %s ) x. ( abs ` %s ) ) e. RR' % (x('j', 'n'), x('k', 'n'))), a1(w, Ajkn, '1re', '1 e. RR'), bq, bq0, uv2_],
              '( %s x. ( ( abs ` %s ) x. ( abs ` %s ) ) ) <_ ( %s x. 1 )' % (b('n'), x('j', 'n'), x('k', 'n'), b('n')))
    b1 = dq('eqtrd', [dq('mulridd', [dq('recnd', [bq], '%s e. CC' % b('n'))], '( %s x. 1 ) = %s' % (b('n'), b('n'))), dq('mullidd', [dq('recnd', [bq], '%s e. CC' % b('n'))], '( 1 x. %s ) = %s' % (b('n'), b('n'))) if False else
                       dq('eqcomd', [dq('mullidd', [dq('recnd', [bq], '%s e. CC' % b('n'))], '( 1 x. %s ) = %s' % (b('n'), b('n')))], '%s = ( 1 x. %s )' % (b('n'), b('n')))], '( %s x. 1 ) = ( 1 x. %s )' % (b('n'), b('n')))
    wb = dq('breqtrd', [dq('eqbrtrd', [aw, bu], '( abs ` ( %s ` n ) ) <_ ( %s x. 1 )' % (WJK, b('n'))), b1], '( abs ` ( %s ` n ) ) <_ ( 1 x. %s )' % (WJK, b('n')))
    Ajku = '( %s /\\ n e. ( ZZ>= ` 1 ) )' % Ajk
    wbu = w.s([D(w, Ajku, 'jca', [w.s([], 'simpl', '( %s -> %s )' % (Ajku, Ajk)), D(w, Ajku, 'eleqtrrdi', [w.s([], 'simpr', '( %s -> n e. ( ZZ>= ` 1 ) )' % Ajku), nu], 'n e. NN')], Ajkn), wb], 'syl',
              '( %s -> ( abs ` ( %s ` n ) ) <_ ( 1 x. ( B ` n ) ) )' % (Ajku, WJK))
    wcv = D(w, Ajk, 'cvgcmpce', [nu, a1(w, Ajk, '1nn', '1 e. NN'), bq, wc, lift(w, h5, Ajk), a1(w, Ajk, '1re', '1 e. RR'), wbu], 'seq 1 ( + , %s ) e. dom ~~>' % WJK)
    pg = partial(Ajk, WJK, GRn, wv, wc, wcv, Ajkn)
    Ajki = '( %s /\\ i e. NN )' % Ajk
    Ajkin = '( %s /\\ n e. ( 1 ... i ) )' % Ajki
    nnq = D(w, Ajkin, 'syl', [w.s([], 'simpr', '( %s -> n e. ( 1 ... i ) )' % Ajkin), w.inst('elfznn')], 'n e. NN')
    grci = w.s([D(w, Ajkin, 'jca', [w.s([], 'simpll', '( %s -> %s )' % (Ajkin, Ajk)), nnq], Ajkn), grc], 'syl', '( %s -> %s e. CC )' % (Ajkin, GRn))
    pgc = D(w, Ajki, 'fsumcl', [D(w, Ajki, 'fzfid', [], '( 1 ... i ) e. Fin'), grci], '%s e. CC' % PG('j', 'k', 'i'))
    LG = '( m e. NN |-> %s )' % PG('j', 'k', 'm')
    lgv = mval(Ajk, PG('j', 'k', 'm'), PG('j', 'k', 'i'), sumsub(GRn), pgc)
    ABG = '( m e. NN |-> ( abs ` %s ) )' % PG('j', 'k', 'm')
    APG = '( abs ` %s )' % PG('j', 'k', 'i')
    apgr = D(w, Ajki, 'abscld', [pgc], '%s e. RR' % APG)
    abgv = mval(Ajk, '( abs ` %s )' % PG('j', 'k', 'm'), APG, w.s([sumsub(GRn)], 'fveq2d', '( m = i -> ( abs ` %s ) = %s )' % (PG('j', 'k', 'm'), APG)), D(w, Ajki, 'recnd', [apgr], '%s e. CC' % APG))
    cag = D(w, Ajk, 'climabs', [nu, pg, a1(w, Ajk, 'mptex', '%s e. _V' % ABG, [w.s([], 'nnex', 'NN e. _V')]), lift(w, one, Ajk), D(w, Ajki, 'eqeltrd', [lgv, pgc], '( %s ` i ) e. CC' % LG),
                                D(w, Ajki, 'eqtr4d', [abgv, D(w, Ajki, 'fveq2d', [lgv], '( abs ` ( %s ` i ) ) = %s' % (LG, APG))], '( %s ` i ) = ( abs ` ( %s ` i ) )' % (ABG, LG))],
            '%s ~~> ( abs ` %s )' % (ABG, GJK))
    # sum over k (context Aj)
    HK = '( m e. NN |-> sum_ k e. J ( abs ` %s ) )' % PG('j', 'k', 'm')
    Aik = '( %s /\\ k e. J )' % Aji
    toAjki = D(w, Aik, 'jca', [D(w, Aik, 'jca', [w.s([], 'simpll', '( %s -> %s )' % (Aik, Aj)), w.s([], 'simpr', '( %s -> k e. J )' % Aik)], Ajk), w.s([], 'simplr', '( %s -> i e. NN )' % Aik)], Ajki)
    sk_i = D(w, Aji, 'fsumrecl', [lift(w, h1, Aji), w.s([toAjki, apgr], 'syl', '( %s -> %s e. RR )' % (Aik, APG))], 'sum_ k e. J %s e. RR' % APG)
    subK = w.s([w.s([sumsub(GRn)], 'fveq2d', '( m = i -> ( abs ` %s ) = %s )' % (PG('j', 'k', 'm'), APG))], 'sumeq2sdv', '( m = i -> sum_ k e. J ( abs ` %s ) = sum_ k e. J %s )' % (PG('j', 'k', 'm'), APG))
    hkv = mval(Aj, 'sum_ k e. J ( abs ` %s )' % PG('j', 'k', 'm'), 'sum_ k e. J %s' % APG, subK, D(w, Aji, 'recnd', [sk_i], 'sum_ k e. J %s e. CC' % APG))
    Aki2 = '( %s /\\ ( k e. J /\\ i e. NN ) )' % Aj
    abc_k = w.s([D(w, Ajki, 'eqeltrd', [abgv, D(w, Ajki, 'recnd', [apgr], '%s e. CC' % APG)], '( %s ` i ) e. CC' % ABG)], 'anasss', '( %s -> ( %s ` i ) e. CC )' % (Aki2, ABG))
    hks = D(w, Aji, 'eqtr4d', [hkv, D(w, Aji, 'sumeq2dv', [w.s([toAjki, abgv], 'syl', '( %s -> ( %s ` i ) = %s )' % (Aik, ABG, APG))], 'sum_ k e. J ( %s ` i ) = sum_ k e. J %s' % (ABG, APG))],
            '( %s ` i ) = sum_ k e. J ( %s ` i )' % (HK, ABG))
    chk = dj('climfsum', [nu, lift(w, one, Aj), lift(w, h1, Aj), cag, a1(w, Aj, 'mptex', '%s e. _V' % HK, [w.s([], 'nnex', 'NN e. _V')]), abc_k, hks],
             '%s ~~> sum_ k e. J ( abs ` %s )' % (HK, GJK))
    # sum over j (context ph)
    QF = '( m e. NN |-> %s )' % QS('m')
    QI = 'sum_ j e. J sum_ k e. J %s' % APG
    qsr = dI('fsumrecl', [lift(w, h1, Ai), w.s([toAji, sk_i], 'syl', '( %s -> sum_ k e. J %s e. RR )' % (Aij, APG))], '%s e. RR' % QI)
    subQ = w.s([subK], 'sumeq2sdv', '( m = i -> %s = %s )' % (QS('m'), QI))
    qfv = mval('ph', QS('m'), QI, subQ, dI('recnd', [qsr], '%s e. CC' % QI))
    hkc = w.s([D(w, Aji, 'eqeltrd', [hkv, D(w, Aji, 'recnd', [sk_i], 'sum_ k e. J %s e. CC' % APG)], '( %s ` i ) e. CC' % HK)], 'anasss', '( %s -> ( %s ` i ) e. CC )' % (Aji2, HK))
    qs = dI('eqtr4d', [qfv, dI('sumeq2dv', [w.s([toAji, hkv], 'syl', '( %s -> ( %s ` i ) = sum_ k e. J %s )' % (Aij, HK, APG))], 'sum_ j e. J ( %s ` i ) = %s' % (HK, QI))],
            '( %s ` i ) = sum_ j e. J ( %s ` i )' % (QF, HK))
    SGK = 'sum_ j e. J sum_ k e. J ( abs ` %s )' % GJK
    cq = d('climfsum', [nu, one, h1, chk, a1(w, A, 'mptex', '%s e. _V' % QF, [w.s([], 'nnex', 'NN e. _V')]), hkc, qs], '%s ~~> %s' % (QF, SGK))
    RF = '( m e. NN |-> %s )' % RHS('m')
    subR = w.s([sumsub(AN('n')), subQ], 'oveq12d', '( m = i -> %s = %s )' % (RHS('m'), '( %s x. %s )' % (SA('i'), QI)))
    rfv = mval('ph', RHS('m'), '( %s x. %s )' % (SA('i'), QI), subR, dI('recnd', [dI('remulcld', [sar_i, qsr], '( %s x. %s ) e. RR' % (SA('i'), QI))], '( %s x. %s ) e. CC' % (SA('i'), QI)))
    rfm = dI('eqtr4d', [rfv, dI('oveq12d', [sav, qfv], '( ( %s ` i ) x. ( %s ` i ) ) = ( %s x. %s )' % (SAm, QF, SA('i'), QI))], '( %s ` i ) = ( ( %s ` i ) x. ( %s ` i ) )' % (RF, SAm, QF))
    cr = d('climmul', [nu, one, pa, a1(w, A, 'mptex', '%s e. _V' % RF, [w.s([], 'nnex', 'NN e. _V')]), cq,
                       dI('eqeltrd', [sav, dI('recnd', [sar_i], '%s e. CC' % SA('i'))], '( %s ` i ) e. CC' % SAm), dI('eqeltrd', [qfv, dI('recnd', [qsr], '%s e. CC' % QI)], '( %s ` i ) e. CC' % QF), rfm],
           '%s ~~> ( %s x. %s )' % (RF, SAI, SGK))
    # ---- (i) climle
    lfr = dI('eqeltrd', [lfv, dI('resqcld', [sumr_i], '%s e. RR' % LHS('i'))], '( %s ` i ) e. RR' % LF)
    rfr = dI('eqeltrd', [rfv, dI('remulcld', [sar_i, qsr], '( %s x. %s ) e. RR' % (SA('i'), QI))], '( %s ` i ) e. RR' % RF)
    # half is stated with the sums as written; QS(i) is QI
    le_i = dI('3brtr4d' if False else 'breq12d' if False else 'eqbrtrd', [lfv, dI('breqtrrd', [half, rfv], '%s <_ ( %s ` i )' % (LHS('i'), RF))], '( %s ` i ) <_ ( %s ` i )' % (LF, RF))
    lim = d('climle', [nu, one, cl, cr, lfr, rfr, le_i], '( %s x. %s ) <_ ( %s x. %s )' % (SFJ, SFJ, SAI, SGK))
    sfr = d('fsumrecl', [h1, dj('abscld', [dj('syl', [pj, w.inst('climcl')], '%s e. CC' % FJ)], '( abs ` %s ) e. RR' % FJ)], '%s e. RR' % SFJ)
    fin = d('eqbrtrd', [d('sqvald', [d('recnd', [sfr], '%s e. CC' % SFJ)], '( %s ^ 2 ) = ( %s x. %s )' % (SFJ, SFJ, SFJ)), lim], split_imp(S['gf1hal'])[1])
    w.qed([fin], 'idi', S['gf1hal'])
    return run(w, only)


if __name__ == '__main__':
    gen_hal()
