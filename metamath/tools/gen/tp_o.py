"""Sortie TP: the analytic core of Turan's second main theorem (tpcore1: for a radius R <_ D avoiding the node distances and
nodes ordered with prefix products >_ ( D / 4 ) ^ ( i + 1 ), a bound C on the window power sums forces
pi <_ 4 D ( 1 / ( 1 - D ) ) ^ ( M + 1 ) ( sum_i 2 ^ i ( 4 / D ) ^ ( i + 1 ) ) C)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
import tplib
from tplib import S, W, Closure, ap, apc, lin, lift, WIN
import cl as _cl
import ef2lib as E
import mvlib
from tp_g import FY, CN0, TPI
from tp_k import DS, AR, BR, FRS, CRS, INSR
from tp_m import WINH, OMJ

only = sys.argv[1:]
conj, up, body_of, top_and, ante_of, tsub = E.conj, E.up, E.body_of, E.top_and, E.ante_of, E.tsub
stmt = tplib.stmt


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


DEX = '( ( N - 1 ) / ( M + N ) )'
Y = '( M + 1 )'
X1 = '( ( 1 / ( 1 - D ) ) ^ %s )' % Y
X1R = '( ( 1 / ( 1 - R ) ) ^ %s )' % Y
GT = '( ( 2 ^ i ) x. ( ( 4 / D ) ^ ( i + 1 ) ) )'
GS = 'sum_ i e. ( 0 ..^ N ) %s' % GT
PREF = 'A. n e. ( 0 ..^ N ) ( ( D / 4 ) ^ ( n + 1 ) ) <_ prod_ y e. ( 0 ..^ ( n + 1 ) ) ( abs ` ( R - %s ) )' % DS('( V ` y )')
H1 = '( ( N e. NN /\\ 2 <_ N /\\ M e. NN0 ) /\\ D = %s )' % DEX
H2 = '( V : ( 0 ..^ N ) --> CC /\\ A. r e. ( 0 ..^ N ) ( abs ` ( V ` r ) ) <_ 1 /\\ ( J e. ( 0 ..^ N ) /\\ ( V ` J ) = 1 ) )'
H3 = '( ( R e. RR /\\ 0 < R /\\ R <_ D ) /\\ A. q e. ( 0 ..^ N ) %s =/= R /\\ %s )' % (DS('( V ` q )'), PREF)
H4 = '( ( C e. RR /\\ 0 <_ C ) /\\ %s )' % WINH
CA = '( ( %s /\\ %s ) /\\ ( %s /\\ %s ) )' % (H1, H2, H3, H4)
S['tpcore1'] = '( %s -> _pi <_ ( ( ( 4 x. D ) x. ( %s x. %s ) ) x. C ) )' % (CA, X1, GS)


def gen_core1():
    w = W('tpcore1', 'The analytic core of Turan\'s second main theorem on the square: with the radius R and the node order of '
               '~ tprad and ~ tpord , a bound C on the window power sums gives ` pi <_ 4 D ( 1 / ( 1 - D ) ) ^ ( M + 1 ) ( sum_i 2 ^ i ( 4 / D ) ^ ( i + 1 ) ) C ` '
               '(Lean ` core_norm_bound ` : ~ tplow against ~ tpupp , ~ tpbb ).')
    A0 = CA
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    h12 = s([], 'simpl', '( %s /\\ %s )' % (H1, H2)); h34 = s([], 'simpr', '( %s /\\ %s )' % (H3, H4))
    h1 = s([h12], 'simpld', H1); h2 = s([h12], 'simprd', H2); h3 = s([h34], 'simpld', H3); h4 = s([h34], 'simprd', H4)
    h1a = s([h1], 'simpld', '( N e. NN /\\ 2 <_ N /\\ M e. NN0 )'); dd = s([h1], 'simprd', 'D = %s' % DEX)
    nn = s([h1a], 'simp1d', 'N e. NN'); n2 = s([h1a], 'simp2d', '2 <_ N'); mm = s([h1a], 'simp3d', 'M e. NN0')
    vf = s([h2], 'simp1d', 'V : ( 0 ..^ N ) --> CC'); vb = s([h2], 'simp2d', 'A. r e. ( 0 ..^ N ) ( abs ` ( V ` r ) ) <_ 1')
    jj = s([h2], 'simp3d', '( J e. ( 0 ..^ N ) /\\ ( V ` J ) = 1 )')
    rrr = s([h3], 'simp1d', '( R e. RR /\\ 0 < R /\\ R <_ D )'); alq = s([h3], 'simp2d', 'A. q e. ( 0 ..^ N ) %s =/= R' % DS('( V ` q )')); pref = s([h3], 'simp3d', PREF)
    rr = s([rrr], 'simp1d', 'R e. RR'); r0 = s([rrr], 'simp2d', '0 < R'); rD = s([rrr], 'simp3d', 'R <_ D')
    c2 = s([h4], 'simpld', '( C e. RR /\\ 0 <_ C )'); wh = s([h4], 'simprd', WINH)
    cr = s([c2], 'simpld', 'C e. RR'); c0 = s([c2], 'simprd', '0 <_ C')
    c = Closure(w, A0, {'N': ('NN', nn), 'M': ('NN0', mm), 'R': ('RR', rr), 'C': ('RR', cr)})
    c.have('C', 'ge0', c0)
    kp = lin.linarith(w, A0, [n2], '0 < ( N - 1 )', closure=c)
    c.have('( N - 1 )', 'gt0', kp)
    drp = s([dd, c.mem(DEX, 'RR+')], 'eqeltrd', 'D e. RR+')
    c.have('D', 'RR+', drp)
    klt = lin.linarith(w, A0, [c.ge0('M')], '( N - 1 ) < ( 1 x. ( M + N ) )', closure=c)
    dlt = s([klt, ap(w, A0, 'ltdivmul2d', '( %s < 1 <-> ( N - 1 ) < ( 1 x. ( M + N ) ) )' % DEX, c)], 'mpbird', '%s < 1' % DEX)
    dlt = s([dd, dlt], 'eqbrtrd', 'D < 1')
    r1 = lin.linarith(w, A0, [rD, dlt], 'R < 1', closure=c)
    # ---- lower bound
    LOW = stmt('tplow')
    la, lc = ante_of(LOW)
    rrr1 = s([rr, r0, r1], '3jca', '( R e. RR /\\ 0 < R /\\ R < 1 )')
    have = {'( R e. RR /\\ 0 < R /\\ R < 1 )': rrr1,
            '( M e. NN0 /\\ N e. NN /\\ V : ( 0 ..^ N ) --> CC )': s([mm, nn, vf], '3jca', '( M e. NN0 /\\ N e. NN /\\ V : ( 0 ..^ N ) --> CC )'),
            'A. q e. ( 0 ..^ N ) %s =/= R' % DS('( V ` q )'): alq, '( J e. ( 0 ..^ N ) /\\ ( V ` J ) = 1 )': jj}
    low = s([conj(w, A0, la, have), w.inst('tplow')], 'syl', lc)
    LAM = lc.split('( abs ` ', 1)[1][:-2]
    # BI ( n ) complex, as a family
    idqr = w.s([], 'id', '( q = r -> q = r )')
    cgqr, nqr = w.wcongr('%s =/= R' % DS('( V ` q )'), {'q': 'r'}, 'q = r', {'q': idqr})
    alr = s([alq, w.s([cgqr], 'cbvralvw', '( A. q e. ( 0 ..^ N ) %s =/= R <-> A. r e. ( 0 ..^ N ) %s )' % (DS('( V ` q )'), nqr))], 'sylib', 'A. r e. ( 0 ..^ N ) %s' % nqr)
    nv0 = s([c.mem('N', 'NN0'), vf], 'jca', '( N e. NN0 /\\ V : ( 0 ..^ N ) --> CC )')
    def bb(lab, K, iv, kss):
        f = tsub(stmt(lab), {'K': '( 0 ..^ ( %s + 1 ) )' % iv, 'Y': Y})
        a, cc = ante_of(f)
        hv = {'( R e. RR /\\ 0 < R /\\ R < 1 )': _cl.lift(w, rrr1, K),
              '( ( M + 1 ) e. NN /\\ ( N e. NN0 /\\ V : ( 0 ..^ N ) --> CC ) /\\ ( 0 ..^ ( %s + 1 ) ) C_ ( 0 ..^ N ) )' % iv:
                  w.s([_cl.lift(w, c.mem(Y, 'NN'), K), _cl.lift(w, nv0, K), kss], '3jca', '( %s -> ( ( M + 1 ) e. NN /\\ ( N e. NN0 /\\ V : ( 0 ..^ N ) --> CC ) /\\ ( 0 ..^ ( %s + 1 ) ) C_ ( 0 ..^ N ) ) )' % (K, iv)),
              body_of(w, alr): _cl.lift(w, alr, K)}
        return w.s([conj(w, K, a, hv), w.inst(lab)], 'syl', '( %s -> %s )' % (K, cc)), cc
    def kss_of(K, iv, iin):
        return w.s([w.s([w.s([iin, w.inst('fzofzp1')], 'syl', '( %s -> ( %s + 1 ) e. ( 0 ... N ) )' % (K, iv)), w.inst('elfzuz3')], 'syl', '( %s -> N e. ( ZZ>= ` ( %s + 1 ) ) )' % (K, iv)),
                    w.inst('fzoss2')], 'syl', '( %s -> ( 0 ..^ ( %s + 1 ) ) C_ ( 0 ..^ N ) )' % (K, iv))
    An = '( %s /\\ x e. ( 0 ..^ N ) )' % A0
    nin = w.s([], 'simpr', '( %s -> x e. ( 0 ..^ N ) )' % An)
    bic, bicc = bb('tpbic', An, 'x', kss_of(An, 'x', nin))
    BIn = bicc.rsplit(' e. CC', 1)[0]
    FB = '( x e. ( 0 ..^ N ) |-> %s )' % BIn
    fbf = s([bic, w.s([], 'eqid', '%s = %s' % (FB, FB))], 'fmptd', '%s : ( 0 ..^ N ) --> CC' % FB)
    # ---- upper bound
    UP = tsub(stmt('tpupp'), {'F': FB})
    ua, uc = ante_of(UP)
    have = {'( N e. NN /\\ M e. NN0 /\\ V : ( 0 ..^ N ) --> CC )': s([nn, mm, vf], '3jca', '( N e. NN /\\ M e. NN0 /\\ V : ( 0 ..^ N ) --> CC )'),
            'A. r e. ( 0 ..^ N ) ( abs ` ( V ` r ) ) <_ 1': vb, 'C e. RR': cr, WINH: wh, '%s : ( 0 ..^ N ) --> CC' % FB: fbf}
    upp = s([conj(w, A0, ua, have), w.inst('tpupp')], 'syl', uc)
    # ( FB ` i ) = BI ( i )
    Ai = '( %s /\\ i e. ( 0 ..^ N ) )' % A0
    iin = w.s([], 'simpr', '( %s -> i e. ( 0 ..^ N ) )' % Ai)
    idni = w.s([], 'id', '( x = i -> x = i )')
    cgni, BIi = w.congr(BIn, {'x': 'i'}, 'x = i', {'x': idni})
    fv0 = w.s([cgni, w.s([], 'eqid', '%s = %s' % (FB, FB)), w.s([], 'ovex', '%s e. _V' % BIi)], 'fvmpt', '( i e. ( 0 ..^ N ) -> ( %s ` i ) = %s )' % (FB, BIi))
    fvi = w.s([iin, fv0], 'syl', '( %s -> ( %s ` i ) = %s )' % (Ai, FB, BIi))
    LAMF = uc.split('( abs ` ', 1)[1].split(' ) <_ sum_ i', 1)[0]
    RHSF = uc.split(' ) <_ ', 1)[1]
    # LAMF = LAM
    Aj = '( %s /\\ j e. ( 0 ..^ N ) )' % A0
    Aji = '( %s /\\ i e. ( 0 ..^ N ) )' % Aj
    fvji = w.s([w.s([], 'simpr', '( %s -> i e. ( 0 ..^ N ) )' % Aji), fv0], 'syl', '( %s -> ( %s ` i ) = %s )' % (Aji, FB, BIi))
    OX = OMJ('i')
    t1 = w.s([fvji], 'oveq1d', '( %s -> ( ( %s ` i ) x. %s ) = ( %s x. %s ) )' % (Aji, FB, OX, BIi, OX))
    t2 = w.s([t1], 'sumeq2dv', '( %s -> sum_ i e. ( 0 ..^ N ) ( ( %s ` i ) x. %s ) = sum_ i e. ( 0 ..^ N ) ( %s x. %s ) )' % (Aj, FB, OX, BIi, OX))
    VY = '( ( V ` j ) ^ %s )' % Y
    t3 = w.s([t2], 'oveq2d', '( %s -> ( %s x. sum_ i e. ( 0 ..^ N ) ( ( %s ` i ) x. %s ) ) = ( %s x. sum_ i e. ( 0 ..^ N ) ( %s x. %s ) ) )' % (Aj, VY, FB, OX, VY, BIi, OX))
    lamf = s([t3], 'sumeq2dv', '%s = sum_ j e. ( 0 ..^ N ) ( %s x. sum_ i e. ( 0 ..^ N ) ( %s x. %s ) )' % (LAMF, VY, BIi, OX))
    LAMb = 'sum_ j e. ( 0 ..^ N ) ( %s x. sum_ i e. ( 0 ..^ N ) ( %s x. %s ) )' % (VY, BIi, OX)
    assert LAMb == LAM, (LAMb[:200], LAM[:200])
    T2 = '( ( 2 ^ i ) x. C )'
    r1_ = w.s([w.s([w.s([fvi], 'fveq2d', '( %s -> ( abs ` ( %s ` i ) ) = ( abs ` %s ) )' % (Ai, FB, BIi))], 'oveq1d',
                   '( %s -> ( ( abs ` ( %s ` i ) ) x. %s ) = ( ( abs ` %s ) x. %s ) )' % (Ai, FB, T2, BIi, T2))], 'sumeq2dv',
              '( %s -> %s = sum_ i e. ( 0 ..^ N ) ( ( abs ` %s ) x. %s ) )' % (A0, RHSF, BIi, T2))
    RHS = 'sum_ i e. ( 0 ..^ N ) ( ( abs ` %s ) x. %s )' % (BIi, T2)
    upp2 = s([s([s([lamf], 'fveq2d', '( abs ` %s ) = ( abs ` %s )' % (LAMF, LAM)), upp], 'eqbrtrrd', '( abs ` %s ) <_ %s' % (LAM, RHSF)), r1_], 'breqtrd',
             '( abs ` %s ) <_ %s' % (LAM, RHS))
    # ---- per-i coefficient bound
    ci = Closure(w, Ai, {'N': ('NN', _cl.lift(w, nn, Ai)), 'M': ('NN0', _cl.lift(w, mm, Ai)), 'R': ('RR', _cl.lift(w, rr, Ai)), 'C': ('RR', _cl.lift(w, cr, Ai)),
                         'D': ('RR+', _cl.lift(w, drp, Ai))})
    ci.have('C', 'ge0', _cl.lift(w, c0, Ai))
    ci.have('i', 'NN0', w.s([iin, w.inst('elfzonn0')], 'syl', '( %s -> i e. NN0 )' % Ai))
    bbi, bbc = bb('tpbb', Ai, 'i', kss_of(Ai, 'i', iin))
    PI_ = 'prod_ g e. ( 0 ..^ ( i + 1 ) ) ( abs ` ( R - %s ) )' % DS('( V ` g )')
    # prefix bound at i
    idn = w.s([], 'id', '( n = i -> n = i )')
    cgn, nn_ = w.wcongr(PREF.split(' e. ( 0 ..^ N ) ', 1)[1], {'n': 'i'}, 'n = i', {'n': idn})
    pri = w.s([iin, _cl.lift(w, pref, Ai), w.s([cgn], 'rspcv', '( i e. ( 0 ..^ N ) -> ( %s -> %s ) )' % (PREF, nn_))], 'sylc', '( %s -> %s )' % (Ai, nn_))
    idyg = w.s([], 'id', '( y = g -> y = g )')
    cyg, _ = w.congr('( abs ` ( R - %s ) )' % DS('( V ` y )'), {'y': 'g'}, 'y = g', {'y': idyg})
    cbp = w.s([cyg], 'cbvprodv', 'prod_ y e. ( 0 ..^ ( i + 1 ) ) ( abs ` ( R - %s ) ) = %s' % (DS('( V ` y )'), PI_))
    DN = '( ( D / 4 ) ^ ( i + 1 ) )'
    prf = w.s([pri, w.s([cbp], 'a1i', '( %s -> prod_ y e. ( 0 ..^ ( i + 1 ) ) ( abs ` ( R - %s ) ) = %s )' % (Ai, DS('( V ` y )'), PI_))], 'breqtrd',
              '( %s -> %s <_ %s )' % (Ai, DN, PI_))
    # PI e. RR, X1R <_ X1
    Aig = '( %s /\\ g e. ( 0 ..^ ( i + 1 ) ) )' % Ai
    kssi = kss_of(Ai, 'i', iin)
    vg = w.s([_cl.lift(w, vf, Aig), w.s([_cl.lift(w, kssi, Aig), w.s([], 'simpr', '( %s -> g e. ( 0 ..^ ( i + 1 ) ) )' % Aig)], 'sseldd', '( %s -> g e. ( 0 ..^ N ) )' % Aig)],
             'ffvelcdmd', '( %s -> ( V ` g ) e. CC )' % Aig)
    cg_ = Closure(w, Aig, {'R': ('RR', _cl.lift(w, rr, Aig)), '( V ` g )': ('CC', vg)}); cg_.atom('( V ` g )')
    pir = w.s([w.s([w.s([], 'fzofi', '( 0 ..^ ( i + 1 ) ) e. Fin')], 'a1i', '( %s -> ( 0 ..^ ( i + 1 ) ) e. Fin )' % Ai), cg_.mem('( abs ` ( R - %s ) )' % DS('( V ` g )'), 'RR')],
              'fprodrecl', '( %s -> %s e. RR )' % (Ai, PI_))
    ci.have(PI_, 'RR', pir); ci.atom(PI_)
    ci.have('( 1 - D )', 'RR+', w.s([ci.mem('( 1 - D )', 'RR'), lin.linarith(w, Ai, [_cl.lift(w, dlt, Ai)], '0 < ( 1 - D )', closure=ci)], 'elrpd', '( %s -> ( 1 - D ) e. RR+ )' % Ai))
    ci.have('( 1 - R )', 'RR+', w.s([ci.mem('( 1 - R )', 'RR'), lin.linarith(w, Ai, [_cl.lift(w, r1, Ai)], '0 < ( 1 - R )', closure=ci)], 'elrpd', '( %s -> ( 1 - R ) e. RR+ )' % Ai))
    omdr = lin.linarith(w, Ai, [_cl.lift(w, rD, Ai)], '( 1 - D ) <_ ( 1 - R )', closure=ci)
    rec = w.s([omdr, ap(w, Ai, 'lerecd', '( ( 1 - D ) <_ ( 1 - R ) <-> ( 1 / ( 1 - R ) ) <_ ( 1 / ( 1 - D ) ) )', ci)], 'mpbid', '( %s -> ( 1 / ( 1 - R ) ) <_ ( 1 / ( 1 - D ) ) )' % Ai)
    x1le = ap(w, Ai, 'leexp1ad', '%s <_ %s' % (X1R, X1), ci, facts=[rec])
    for t in (X1R, X1):
        ci.have(t, 'RR', ci.mem(t, 'RR')); ci.atom(t)
    ci.have(DN, 'RR+', ci.mem(DN, 'RR+')); ci.atom(DN)
    q1 = ap(w, Ai, 'lediv12ad', '( %s / %s ) <_ ( %s / %s )' % (X1R, PI_, X1, DN), ci, facts=[x1le, prf])
    # X1 / ( D / 4 ) ^ ( i + 1 ) = X1 ( 4 / D ) ^ ( i + 1 )
    F4 = '( ( 4 / D ) ^ ( i + 1 ) )'
    ci.have('( D / 4 )', 'CC', ci.mem('( D / 4 )', 'CC')); ci.have('( D / 4 )', 'ne0', ci.ne0('( D / 4 )'))
    e1 = ap(w, Ai, 'recdivd', '( 1 / ( D / 4 ) ) = ( 4 / D )', ci)
    e2 = ap(w, Ai, 'exprecd', '( ( 1 / ( D / 4 ) ) ^ ( i + 1 ) ) = ( 1 / %s )' % DN, ci)
    e3 = w.s([e2, w.s([e1], 'oveq1d', '( %s -> ( ( 1 / ( D / 4 ) ) ^ ( i + 1 ) ) = %s )' % (Ai, F4))], 'eqtr3d', '( %s -> ( 1 / %s ) = %s )' % (Ai, DN, F4))
    e4 = ap(w, Ai, 'divrecd', '( %s / %s ) = ( %s x. ( 1 / %s ) )' % (X1, DN, X1, DN), ci)
    e5 = w.s([e4, w.s([e3], 'oveq2d', '( %s -> ( %s x. ( 1 / %s ) ) = ( %s x. %s ) )' % (Ai, X1, DN, X1, F4))], 'eqtrd', '( %s -> ( %s / %s ) = ( %s x. %s ) )' % (Ai, X1, DN, X1, F4))
    q2 = w.s([q1, e5], 'breqtrd', '( %s -> ( %s / %s ) <_ ( %s x. %s ) )' % (Ai, X1R, PI_, X1, F4))
    ci.have('_pi', 'RR+', w.s([w.s([], 'pirp', '_pi e. RR+')], 'a1i', '( %s -> _pi e. RR+ )' % Ai))
    q3 = ap(w, Ai, 'lediv1dd', '( ( 4 x. R ) / _pi ) <_ ( ( 4 x. D ) / _pi )', ci, facts=[lin.linarith(w, Ai, [_cl.lift(w, rD, Ai)], '( 4 x. R ) <_ ( 4 x. D )', closure=ci)])
    # the ratio X1R / PI is nonnegative and PI > 0
    ci.have(PI_, 'gt0', lin.linarith(w, Ai, [prf, ci.gt0(DN)], '0 < %s' % PI_, closure=ci))
    for t in ('( ( 4 x. R ) / _pi )', '( ( 4 x. D ) / _pi )', '( %s / %s )' % (X1R, PI_), F4):
        ci.have(t, 'RR', ci.mem(t, 'RR'))
    ci.have('( 4 x. R )', 'ge0', lin.linarith(w, Ai, [_cl.lift(w, r0, Ai)], '0 <_ ( 4 x. R )', closure=ci))
    q4 = ap(w, Ai, 'lemul12ad', '( ( ( 4 x. R ) / _pi ) x. ( %s / %s ) ) <_ ( ( ( 4 x. D ) / _pi ) x. ( %s x. %s ) )' % (X1R, PI_, X1, F4), ci, facts=[q3, q2])
    BA_ = '( abs ` %s )' % BIi
    bici = bb('tpbic', Ai, 'i', kssi)[0]
    ci.have(BA_, 'RR', w.s([bici], 'abscld', '( %s -> %s e. RR )' % (Ai, BA_))); ci.atom(BA_)
    bb2 = w.s([ci.mem(BA_, 'RR'), ci.mem('( ( ( 4 x. R ) / _pi ) x. ( %s / %s ) )' % (X1R, PI_), 'RR'), ci.mem('( ( ( 4 x. D ) / _pi ) x. ( %s x. %s ) )' % (X1, F4), 'RR'), bbi, q4],
              'letrd', '( %s -> ( abs ` %s ) <_ ( ( ( 4 x. D ) / _pi ) x. ( %s x. %s ) ) )' % (Ai, BIi, X1, F4))
    q5 = ap(w, Ai, 'lemul1ad', '( %s x. %s ) <_ ( ( ( ( 4 x. D ) / _pi ) x. ( %s x. %s ) ) x. %s )' % (BA_, T2, X1, F4, T2), ci, facts=[bb2])
    K0 = '( ( ( 4 x. D ) / _pi ) x. ( %s x. C ) )' % X1
    for t in ('( ( 4 x. D ) / _pi )', X1, F4, '( 2 ^ i )', 'C'):
        ci.atom(t)
    q6 = mvlib.ringeq(w, Ai, '( ( ( ( 4 x. D ) / _pi ) x. ( %s x. %s ) ) x. %s )' % (X1, F4, T2), '( %s x. %s )' % (K0, GT), ci)
    pti = w.s([q5, q6], 'breqtrd', '( %s -> ( %s x. %s ) <_ ( %s x. %s ) )' % (Ai, BA_, T2, K0, GT))
    fz = s([w.s([], 'fzofi', '( 0 ..^ N ) e. Fin')], 'a1i', '( 0 ..^ N ) e. Fin')
    sl = s([fz, ci.mem('( %s x. %s )' % (BA_, T2), 'RR'), ci.mem('( %s x. %s )' % (K0, GT), 'RR'), pti], 'fsumle',
           '%s <_ sum_ i e. ( 0 ..^ N ) ( %s x. %s )' % (RHS, K0, GT))
    c.have('_pi', 'RR+', s([w.s([], 'pirp', '_pi e. RR+')], 'a1i', '_pi e. RR+'))
    c.have('D', 'RR+', drp)
    k0c = c.mem(K0, 'CC')
    sm = s([fz, k0c, ci.mem(GT, 'CC')], 'fsummulc2', '( %s x. %s ) = sum_ i e. ( 0 ..^ N ) ( %s x. %s )' % (K0, GS, K0, GT))
    sl2 = s([sl, sm], 'breqtrrd', '%s <_ ( %s x. %s )' % (RHS, K0, GS))
    gsr = s([fz, ci.mem(GT, 'RR')], 'fsumrecl', '%s e. RR' % GS)
    c.have(GS, 'RR', gsr)
    rhsr = s([fz, ci.mem('( %s x. %s )' % (BA_, T2), 'RR')], 'fsumrecl', '%s e. RR' % RHS)
    # LAM e. CC
    Ljj = lambda st: _cl.lift(w, st, Aji)
    jin2 = w.s([], 'simplr', '( %s -> j e. ( 0 ..^ N ) )' % Aji); iin2 = w.s([], 'simpr', '( %s -> i e. ( 0 ..^ N ) )' % Aji)
    bij = bb('tpbic', Aji, 'i', kss_of(Aji, 'i', iin2))[0]
    Ajih = '( %s /\\ h e. ( 0 ..^ i ) )' % Aji
    issj = w.s([w.s([w.s([iin2, w.inst('elfzofz')], 'syl', '( %s -> i e. ( 0 ... N ) )' % Aji), w.inst('elfzuz3')], 'syl', '( %s -> N e. ( ZZ>= ` i ) )' % Aji), w.inst('fzoss2')],
               'syl', '( %s -> ( 0 ..^ i ) C_ ( 0 ..^ N ) )' % Aji)
    vjh = w.s([_cl.lift(w, vf, Ajih), w.s([_cl.lift(w, issj, Ajih), w.s([], 'simpr', '( %s -> h e. ( 0 ..^ i ) )' % Ajih)], 'sseldd', '( %s -> h e. ( 0 ..^ N ) )' % Ajih)],
              'ffvelcdmd', '( %s -> ( V ` h ) e. CC )' % Ajih)
    vjj = w.s([_cl.lift(w, vf, Ajih), _cl.lift(w, jin2, Ajih)], 'ffvelcdmd', '( %s -> ( V ` j ) e. CC )' % Ajih)
    cjh = Closure(w, Ajih, {'( V ` h )': ('CC', vjh), '( V ` j )': ('CC', vjj)}); cjh.atom('( V ` h )'); cjh.atom('( V ` j )')
    oxc = w.s([w.s([w.s([], 'fzofi', '( 0 ..^ i ) e. Fin')], 'a1i', '( %s -> ( 0 ..^ i ) e. Fin )' % Aji), cjh.mem('( ( V ` j ) - ( V ` h ) )', 'CC')], 'fprodcl', '( %s -> %s e. CC )' % (Aji, OX))
    inner = w.s([_cl.lift(w, fz, Aj), w.s([bij, oxc], 'mulcld', '( %s -> ( %s x. %s ) e. CC )' % (Aji, BIi, OX))], 'fsumcl', '( %s -> sum_ i e. ( 0 ..^ N ) ( %s x. %s ) e. CC )' % (Aj, BIi, OX))
    vyc = w.s([w.s([_cl.lift(w, vf, Aj), w.s([], 'simpr', '( %s -> j e. ( 0 ..^ N ) )' % Aj)], 'ffvelcdmd', '( %s -> ( V ` j ) e. CC )' % Aj), _cl.lift(w, c.mem(Y, 'NN0'), Aj)], 'expcld', '( %s -> %s e. CC )' % (Aj, VY))
    lamc = s([fz, w.s([vyc, inner], 'mulcld', '( %s -> ( %s x. sum_ i e. ( 0 ..^ N ) ( %s x. %s ) ) e. CC )' % (Aj, VY, BIi, OX))], 'fsumcl', '%s e. CC' % LAM)
    labr = s([lamc], 'abscld', '( abs ` %s ) e. RR' % LAM)
    c.have(GS, 'RR', gsr)
    kgr = c.mem('( %s x. %s )' % (K0, GS), 'RR')
    l2 = s([labr, rhsr, kgr, upp2, sl2], 'letrd', '( abs ` %s ) <_ ( %s x. %s )' % (LAM, K0, GS))
    one = s([s([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR'), labr, kgr, low, l2], 'letrd', '1 <_ ( %s x. %s )' % (K0, GS))
    c.have(GS, 'RR', gsr); c.atom(GS)
    c.atom(X1); c.have(X1, 'RR', c.mem(X1, 'RR'))
    QQ = '( %s x. %s )' % (K0, GS)
    c.have(QQ, 'RR', c.mem(QQ, 'RR')); c.atom(QQ)
    pm = ap(w, A0, 'lemul2ad', '( _pi x. 1 ) <_ ( _pi x. %s )' % QQ, c, facts=[one])
    pm1 = ap(w, A0, 'mulridd', '( _pi x. 1 ) = _pi', c)
    PD4 = '( ( 4 x. D ) / _pi )'
    dc = ap(w, A0, 'divcan2d', '( _pi x. %s ) = ( 4 x. D )' % PD4, c)
    for t in ('_pi', PD4, 'C'):
        c.atom(t)
    cq = Closure(w, A0, {})
    for t_ in ('_pi', PD4, X1, 'C', GS):
        cq.have(t_, 'CC', c.mem(t_, 'CC')); cq.atom(t_)
    re1 = mvlib.ringeq(w, A0, '( _pi x. %s )' % QQ, '( ( _pi x. %s ) x. ( ( %s x. C ) x. %s ) )' % (PD4, X1, GS), cq)
    re2 = s([dc], 'oveq1d', '( ( _pi x. %s ) x. ( ( %s x. C ) x. %s ) ) = ( ( 4 x. D ) x. ( ( %s x. C ) x. %s ) )' % (PD4, X1, GS, X1, GS))
    c.have('( 4 x. D )', 'CC', c.mem('( 4 x. D )', 'CC')); c.atom('( 4 x. D )')
    cq.have('( 4 x. D )', 'CC', c.mem('( 4 x. D )', 'CC')); cq.atom('( 4 x. D )')
    re3 = mvlib.ringeq(w, A0, '( ( 4 x. D ) x. ( ( %s x. C ) x. %s ) )' % (X1, GS), '( ( ( 4 x. D ) x. ( %s x. %s ) ) x. C )' % (X1, GS), cq)
    req_ = s([re1, re2, re3], '3eqtrd', '( _pi x. %s ) = ( ( ( 4 x. D ) x. ( %s x. %s ) ) x. C )' % (QQ, X1, GS))
    w.qed([pm1, pm, req_], '3brtr3d', S['tpcore1'])
    return run(w)


if __name__ == '__main__':
    gen_core1()
