"""Sortie TP: the two sides of the Turan functional on the square (tplow: the Newton interpolant sums to the count of
inside nodes, at least 1; tpupp: the same sum is at most sum_i abs b_i 2 ^ i C)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
import tplib
from tplib import S, W, Closure, ap, apc, lin, lift, WIN
import cl as _cl
import ef2lib as E
import mvlib
from tp_g import FY, CN0, TPI
from tp_k import DS, RA, IA, AR, BR, FRS, CRS, INSR, sqbase

only = sys.argv[1:]
conj, up, body_of, top_and, ante_of, tsub = E.conj, E.up, E.body_of, E.top_and, E.ante_of, E.tsub
stmt = tplib.stmt


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


SQS = {'P': '( 1 - R )', 'Q': '( 1 + R )', 'S': '-u R', 'T': 'R', 'Y': '( M + 1 )'}


def node_inst(J):
    m = dict(SQS); m['J'] = J
    return ante_of(tsub(stmt('tpnode'), m))


NA_j, NC_j = node_inst('j')
LHS_j = NC_j.split(' = if ( ')[0]          # sum_ i e. ( 0 ..^ N ) ( BI(i) x. OMX_j(i) )
Y = '( M + 1 )'
LAM = 'sum_ j e. ( 0 ..^ N ) ( ( ( V ` j ) ^ %s ) x. %s )' % (Y, LHS_j)
BASE = '( ( R e. RR /\\ 0 < R /\\ R < 1 ) /\\ ( ( M e. NN0 /\\ N e. NN /\\ V : ( 0 ..^ N ) --> CC ) /\\ A. q e. ( 0 ..^ N ) %s =/= R ) )' % DS('( V ` q )')
LA = '( %s /\\ ( J e. ( 0 ..^ N ) /\\ ( V ` J ) = 1 ) )' % BASE
S['tplow'] = '( %s -> 1 <_ ( abs ` %s ) )' % (LA, LAM)


def nodes(w, K, c, rr, r0, vf, alq):
    """( K -> A. r e. ( 0 ..^ N ) ( -. ( V ` r ) e. FRS /\\ ( ( V ` r ) e. CRS -> INSR ) ) ) and a per-index tpsqv helper"""
    def sqv(Kc, iv, iin):
        vi = w.s([_cl.lift(w, vf, Kc), iin], 'ffvelcdmd', '( %s -> ( V ` %s ) e. CC )' % (Kc, iv))
        idq = w.s([], 'id', '( q = %s -> q = %s )' % (iv, iv))
        cg, nw = w.wcongr('%s =/= R' % DS('( V ` q )'), {'q': iv}, 'q = %s' % iv, {'q': idq})
        dq = w.s([iin, _cl.lift(w, alq, Kc), w.s([cg], 'rspcv', '( %s e. ( 0 ..^ N ) -> ( A. q e. ( 0 ..^ N ) %s =/= R -> %s ) )' % (iv, DS('( V ` q )'), nw))], 'sylc', '( %s -> %s )' % (Kc, nw))
        V_ = '( V ` %s )' % iv
        return vi, w.s([w.s([w.s([_cl.lift(w, rr, Kc), _cl.lift(w, r0, Kc)], 'jca', '( %s -> ( R e. RR /\\ 0 < R ) )' % Kc), w.s([vi, dq], 'jca', '( %s -> ( %s e. CC /\\ %s ) )' % (Kc, V_, nw))],
                            'jca', '( %s -> ( ( R e. RR /\\ 0 < R ) /\\ ( %s e. CC /\\ %s ) ) )' % (Kc, V_, nw)), w.inst('tpsqv')], 'syl',
                       '( %s -> ( -. %s e. %s /\\ ( %s e. %s -> %s ) /\\ ( %s <-> %s < R ) ) )' % (Kc, V_, FRS, V_, CRS, INSR(V_), INSR(V_), DS(V_)))
    Kr = '( %s /\\ r e. ( 0 ..^ N ) )' % K
    _, sv = sqv(Kr, 'r', w.s([], 'simpr', '( %s -> r e. ( 0 ..^ N ) )' % Kr))
    V_ = '( V ` r )'
    pr = w.s([w.s([sv], 'simp1d', '( %s -> -. %s e. %s )' % (Kr, V_, FRS)), w.s([sv], 'simp2d', '( %s -> ( %s e. %s -> %s ) )' % (Kr, V_, CRS, INSR(V_)))], 'jca',
             '( %s -> ( -. %s e. %s /\\ ( %s e. %s -> %s ) ) )' % (Kr, V_, FRS, V_, CRS, INSR(V_)))
    al = w.s([pr], 'ralrimiva', '( %s -> A. r e. ( 0 ..^ N ) ( -. %s e. %s /\\ ( %s e. %s -> %s ) ) )' % (K, V_, FRS, V_, CRS, INSR(V_)))
    return al, sqv


def gen_low():
    w = W('tplow', 'The Newton interpolant of ` z ^ - ( M + 1 ) ` on the square takes the value ` v_j ^ - ( M + 1 ) ` at the nodes inside and 0 outside, '
               'so ` sum_j v_j ^ ( M + 1 ) P ( v_j ) ` counts the inside nodes; the node ` v_J = 1 ` is inside, so the count is at least 1.')
    A0 = LA
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    b = s([], 'simpl', BASE); jj = s([], 'simpr', '( J e. ( 0 ..^ N ) /\\ ( V ` J ) = 1 )')
    rrr = s([b], 'simpld', '( R e. RR /\\ 0 < R /\\ R < 1 )')
    rr = s([rrr], 'simp1d', 'R e. RR'); r0 = s([rrr], 'simp2d', '0 < R'); r1 = s([rrr], 'simp3d', 'R < 1')
    b2 = s([b], 'simprd', '( ( M e. NN0 /\\ N e. NN /\\ V : ( 0 ..^ N ) --> CC ) /\\ A. q e. ( 0 ..^ N ) %s =/= R )' % DS('( V ` q )'))
    mnv = s([b2], 'simpld', '( M e. NN0 /\\ N e. NN /\\ V : ( 0 ..^ N ) --> CC )'); alq = s([b2], 'simprd', 'A. q e. ( 0 ..^ N ) %s =/= R' % DS('( V ` q )'))
    mm = s([mnv], 'simp1d', 'M e. NN0'); nn = s([mnv], 'simp2d', 'N e. NN'); vf = s([mnv], 'simp3d', 'V : ( 0 ..^ N ) --> CC')
    jn = s([jj], 'simpld', 'J e. ( 0 ..^ N )'); vj1 = s([jj], 'simprd', '( V ` J ) = 1')
    c = Closure(w, A0, {'R': ('RR', rr), 'M': ('NN0', mm), 'N': ('NN', nn)})
    d = sqbase(w, A0, c)
    al, sqv = nodes(w, A0, c, rr, r0, vf, alq)
    # tpnode at each j
    Aj = '( %s /\\ j e. ( 0 ..^ N ) )' % A0
    Lj = lambda st: _cl.lift(w, st, Aj)
    cj = Closure(w, Aj, {'R': ('RR', Lj(rr)), 'M': ('NN0', Lj(mm)), 'N': ('NN', Lj(nn))})
    omr = lin.linarith(w, Aj, [Lj(r1)], '0 < ( 1 - R )', closure=cj)
    geo = lin.linarith(w, Aj, [Lj(r0)], '( 1 - R ) <_ ( 1 + R )', closure=cj)
    geo2 = lin.linarith(w, Aj, [Lj(r0)], '-u R <_ R', closure=cj)
    jin = w.s([], 'simpr', '( %s -> j e. ( 0 ..^ N ) )' % Aj)
    have = {'( ( 1 - R ) e. RR /\\ ( 1 + R ) e. RR )': w.s([cj.mem('( 1 - R )', 'RR'), cj.mem('( 1 + R )', 'RR')], 'jca', '( %s -> ( ( 1 - R ) e. RR /\\ ( 1 + R ) e. RR ) )' % Aj),
            '( -u R e. RR /\\ R e. RR )': w.s([cj.mem('-u R', 'RR'), Lj(rr)], 'jca', '( %s -> ( -u R e. RR /\\ R e. RR ) )' % Aj),
            '( 0 < ( 1 - R ) /\\ ( 1 - R ) <_ ( 1 + R ) /\\ -u R <_ R )': w.s([omr, geo, geo2], '3jca', '( %s -> ( 0 < ( 1 - R ) /\\ ( 1 - R ) <_ ( 1 + R ) /\\ -u R <_ R ) )' % Aj),
            '( ( M + 1 ) e. NN /\\ N e. NN /\\ V : ( 0 ..^ N ) --> CC )': w.s([cj.mem(Y, 'NN'), Lj(nn), Lj(vf)], '3jca', '( %s -> ( ( M + 1 ) e. NN /\\ N e. NN /\\ V : ( 0 ..^ N ) --> CC ) )' % Aj),
            body_of(w, al): Lj(al), 'j e. ( 0 ..^ N )': jin}
    nd = w.s([conj(w, Aj, NA_j, have), w.inst('tpnode')], 'syl', '( %s -> %s )' % (Aj, NC_j))
    VJ = '( V ` j )'
    IFV = NC_j.split(' = ', 1)[1]
    INSj = INSR(VJ)
    vjc, svj = sqv(Aj, 'j', jin)
    # term_j = if ( INS , 1 , 0 )
    T = '( ( %s ^ %s ) x. %s )' % (VJ, Y, LHS_j)
    te1 = w.s([nd], 'oveq2d', '( %s -> %s = ( ( %s ^ %s ) x. %s ) )' % (Aj, T, VJ, Y, IFV))
    IF1 = 'if ( %s , 1 , 0 )' % INSj
    Ci = '( %s /\\ %s )' % (Aj, INSj)
    Li = lambda st: _cl.lift(w, st, Ci)
    ins = w.s([], 'simpr', '( %s -> %s )' % (Ci, INSj))
    vcr = w.s([Li(d['ab']), w.s([Li(vjc), ins], 'jca', '( %s -> ( %s e. CC /\\ %s ) )' % (Ci, VJ, INSj)), w.inst('crectinp')], 'syl2anc', '( %s -> %s e. %s )' % (Ci, VJ, CRS))
    ra0 = w.s([lin.linarith(w, Ci, [Li(Lj(r1))], '0 < ( 1 - R )', closure=Closure(w, Ci, {'R': ('RR', Li(Lj(rr)))})), Li(d['ra'])], 'breqtrrd', '( %s -> 0 < ( Re ` %s ) )' % (Ci, AR))
    rh = w.s([w.s([Li(d['ab']), ra0], 'jca', '( %s -> ( ( %s e. CC /\\ %s e. CC ) /\\ 0 < ( Re ` %s ) ) )' % (Ci, AR, BR, AR)), w.inst('ef2rhp')], 'syl',
             '( %s -> ( %s C_ %s /\\ %s C_ %s ) )' % (Ci, CRS, E.HP0, CRS, CN0))
    vcn = w.s([w.s([rh], 'simprd', '( %s -> %s C_ %s )' % (Ci, CRS, CN0)), vcr], 'sseldd', '( %s -> %s e. %s )' % (Ci, VJ, CN0))
    vn0 = w.s([w.s([vcn, w.s([], 'eldifsn', '( %s e. %s <-> ( %s e. CC /\\ %s =/= 0 ) )' % (VJ, CN0, VJ, VJ))], 'sylib', '( %s -> ( %s e. CC /\\ %s =/= 0 ) )' % (Ci, VJ, VJ)),
               w.inst('simpr')], 'syl', '( %s -> %s =/= 0 )' % (Ci, VJ))
    ci = Closure(w, Ci, {VJ: ('CC', Li(vjc)), 'M': ('NN0', Li(Lj(mm)))}); ci.have(VJ, 'ne0', vn0); ci.atom(VJ)
    k1 = w.s([w.s([ins], 'iftrued', '( %s -> %s = ( ( 1 / %s ) ^ %s ) )' % (Ci, IFV, VJ, Y))], 'oveq2d',
             '( %s -> ( ( %s ^ %s ) x. %s ) = ( ( %s ^ %s ) x. ( ( 1 / %s ) ^ %s ) ) )' % (Ci, VJ, Y, IFV, VJ, Y, VJ, Y))
    k2 = ap(w, Ci, 'mulexpd', '( ( %s x. ( 1 / %s ) ) ^ %s ) = ( ( %s ^ %s ) x. ( ( 1 / %s ) ^ %s ) )' % (VJ, VJ, Y, VJ, Y, VJ, Y), ci)
    k3 = w.s([ap(w, Ci, 'recidd', '( %s x. ( 1 / %s ) ) = 1' % (VJ, VJ), ci)], 'oveq1d', '( %s -> ( ( %s x. ( 1 / %s ) ) ^ %s ) = ( 1 ^ %s ) )' % (Ci, VJ, VJ, Y, Y))
    k4 = w.s([ci.mem(Y, 'ZZ'), w.inst('1exp')], 'syl', '( %s -> ( 1 ^ %s ) = 1 )' % (Ci, Y))
    k5 = w.s([k2, k3, k4], '3eqtr3d', '( %s -> ( ( %s ^ %s ) x. ( ( 1 / %s ) ^ %s ) ) = 1 )' % (Ci, VJ, Y, VJ, Y))
    case1 = w.s([w.s([k1, k5], 'eqtrd', '( %s -> ( ( %s ^ %s ) x. %s ) = 1 )' % (Ci, VJ, Y, IFV)), w.s([ins], 'iftrued', '( %s -> %s = 1 )' % (Ci, IF1))], 'eqtr4d',
                '( %s -> ( ( %s ^ %s ) x. %s ) = %s )' % (Ci, VJ, Y, IFV, IF1))
    Cn = '( %s /\\ -. %s )' % (Aj, INSj)
    nin = w.s([], 'simpr', '( %s -> -. %s )' % (Cn, INSj))
    cn_ = Closure(w, Cn, {VJ: ('CC', _cl.lift(w, vjc, Cn)), 'M': ('NN0', _cl.lift(w, Lj(mm), Cn))}); cn_.atom(VJ)
    n1 = w.s([w.s([nin], 'iffalsed', '( %s -> %s = 0 )' % (Cn, IFV))], 'oveq2d', '( %s -> ( ( %s ^ %s ) x. %s ) = ( ( %s ^ %s ) x. 0 ) )' % (Cn, VJ, Y, IFV, VJ, Y))
    n2 = ap(w, Cn, 'mul01d', '( ( %s ^ %s ) x. 0 ) = 0' % (VJ, Y), cn_)
    case2 = w.s([w.s([n1, n2], 'eqtrd', '( %s -> ( ( %s ^ %s ) x. %s ) = 0 )' % (Cn, VJ, Y, IFV)), w.s([nin], 'iffalsed', '( %s -> %s = 0 )' % (Cn, IF1))], 'eqtr4d',
                '( %s -> ( ( %s ^ %s ) x. %s ) = %s )' % (Cn, VJ, Y, IFV, IF1))
    tj = w.s([te1, w.s([case1, case2], 'pm2.61dan', '( %s -> ( ( %s ^ %s ) x. %s ) = %s )' % (Aj, VJ, Y, IFV, IF1))], 'eqtrd', '( %s -> %s = %s )' % (Aj, T, IF1))
    SI = 'sum_ j e. ( 0 ..^ N ) %s' % IF1
    se = s([tj], 'sumeq2dv', '%s = %s' % (LAM, SI))
    # the sum of indicators is >_ 1: the node J = 1 is inside
    fz = s([w.s([], 'fzofi', '( 0 ..^ N ) e. Fin')], 'a1i', '( 0 ..^ N ) e. Fin')
    ir = w.s([w.s([], '1red', '( %s -> 1 e. RR )' % Aj), w.s([], '0red', '( %s -> 0 e. RR )' % Aj)], 'ifcld', '( %s -> %s e. RR )' % (Aj, IF1))
    z1 = w.s([w.s([], '0le1', '0 <_ 1')], 'a1i', '( %s -> 0 <_ 1 )' % Aj)
    z0 = w.s([w.s([], '0le0', '0 <_ 0')], 'a1i', '( %s -> 0 <_ 0 )' % Aj)
    # 0 <_ if ( ph , 1 , 0 ): by cases
    Pi_ = '( %s /\\ %s )' % (Aj, INSj)
    g1 = w.s([_cl.lift(w, z1, Pi_), w.s([w.s([], 'simpr', '( %s -> %s )' % (Pi_, INSj))], 'iftrued', '( %s -> %s = 1 )' % (Pi_, IF1))], 'breqtrrd', '( %s -> 0 <_ %s )' % (Pi_, IF1))
    Pn_ = '( %s /\\ -. %s )' % (Aj, INSj)
    g2 = w.s([_cl.lift(w, z0, Pn_), w.s([w.s([], 'simpr', '( %s -> -. %s )' % (Pn_, INSj))], 'iffalsed', '( %s -> %s = 0 )' % (Pn_, IF1))], 'breqtrrd', '( %s -> 0 <_ %s )' % (Pn_, IF1))
    ig = w.s([g1, g2], 'pm2.61dan', '( %s -> 0 <_ %s )' % (Aj, IF1))
    idjJ = w.s([], 'id', '( j = J -> j = J )')
    cgJ, nJ = w.congr(IF1, {'j': 'J'}, 'j = J', {'j': idjJ})
    ge1 = s([fz, ir, ig, cgJ, jn], 'fsumge1', '%s <_ %s' % (nJ, SI))
    # at J: V_J = 1 is inside
    VJJ = '( V ` J )'
    vjc_, svJ = sqv(A0, 'J', jn)
    iffJ = s([svJ], 'simp3d', '( %s <-> %s < R )' % (INSR(VJJ), DS(VJJ)))
    # DS ( V ` J ) = 0
    d1 = s([s([vj1], 'oveq1d', '( %s - 1 ) = ( 1 - 1 )' % VJJ), s([w.s([], '1m1e0', '( 1 - 1 ) = 0')], 'a1i', '( 1 - 1 ) = 0')], 'eqtrd', '( %s - 1 ) = 0' % VJJ)
    ra_ = s([s([s([d1], 'fveq2d', '( Re ` ( %s - 1 ) ) = ( Re ` 0 )' % VJJ), s([w.s([], 're0', '( Re ` 0 ) = 0')], 'a1i', '( Re ` 0 ) = 0')], 'eqtrd', '( Re ` ( %s - 1 ) ) = 0' % VJJ)],
            'fveq2d', '%s = ( abs ` 0 )' % RA(VJJ))
    ra_ = s([ra_, s([w.s([], 'abs0', '( abs ` 0 ) = 0')], 'a1i', '( abs ` 0 ) = 0')], 'eqtrd', '%s = 0' % RA(VJJ))
    ia_ = s([s([s([d1], 'fveq2d', '( Im ` ( %s - 1 ) ) = ( Im ` 0 )' % VJJ), s([w.s([], 'im0', '( Im ` 0 ) = 0')], 'a1i', '( Im ` 0 ) = 0')], 'eqtrd', '( Im ` ( %s - 1 ) ) = 0' % VJJ)],
            'fveq2d', '%s = ( abs ` 0 )' % IA(VJJ))
    ia_ = s([ia_, s([w.s([], 'abs0', '( abs ` 0 ) = 0')], 'a1i', '( abs ` 0 ) = 0')], 'eqtrd', '%s = 0' % IA(VJJ))
    dz = s([s([s([ra_, ia_], 'breq12d', '( %s <_ %s <-> 0 <_ 0 )' % (RA(VJJ), IA(VJJ))), ia_, ra_], 'ifbieq12d', '%s = if ( 0 <_ 0 , 0 , 0 )' % DS(VJJ)),
            s([w.s([], 'ifid', 'if ( 0 <_ 0 , 0 , 0 ) = 0')], 'a1i', 'if ( 0 <_ 0 , 0 , 0 ) = 0')], 'eqtrd', '%s = 0' % DS(VJJ))
    dlt = s([dz, r0], 'eqbrtrd', '%s < R' % DS(VJJ))
    insJ = s([dlt, iffJ], 'mpbird', INSR(VJJ))
    one = s([insJ], 'iftrued', '%s = 1' % nJ)
    ge1b = s([one, ge1], 'eqbrtrrd', '1 <_ %s' % SI)
    sir = s([fz, ir], 'fsumrecl', '%s e. RR' % SI)
    si0 = lin.linarith(w, A0, [ge1b], '0 <_ %s' % SI, leaves={SI: sir})
    ab = s([s([se], 'fveq2d', '( abs ` %s ) = ( abs ` %s )' % (LAM, SI)), s([sir, si0], 'absidd', '( abs ` %s ) = %s' % (SI, SI))], 'eqtrd', '( abs ` %s ) = %s' % (LAM, SI))
    w.qed([ge1b, ab], 'breqtrrd', S['tplow'])
    return run(w)


from tp_m import WINH, OMJ
UA = ('( ( N e. NN /\\ M e. NN0 /\\ V : ( 0 ..^ N ) --> CC ) /\\ ( A. r e. ( 0 ..^ N ) ( abs ` ( V ` r ) ) <_ 1 /\\ ( C e. RR /\\ %s ) ) /\\ '
      'F : ( 0 ..^ N ) --> CC )' % WINH)
LAMB = 'sum_ j e. ( 0 ..^ N ) ( ( ( V ` j ) ^ ( M + 1 ) ) x. sum_ i e. ( 0 ..^ N ) ( ( F ` i ) x. %s ) )' % OMJ('i')
S['tpupp'] = '( %s -> ( abs ` %s ) <_ sum_ i e. ( 0 ..^ N ) ( ( abs ` ( F ` i ) ) x. ( ( 2 ^ i ) x. C ) ) )' % (UA, LAMB)


def gen_upp():
    w = W('tpupp', 'The Turan functional of the Newton sum ` sum_i B_i prod_( h < i ) ( X - v_h ) ` is at most ` sum_i abs B_i 2 ^ i C ` '
               '(swap the sums, then ~ tplam ).')
    A0 = UA
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    t1 = s([], 'simp1', '( N e. NN /\\ M e. NN0 /\\ V : ( 0 ..^ N ) --> CC )')
    t2 = s([], 'simp2', '( A. r e. ( 0 ..^ N ) ( abs ` ( V ` r ) ) <_ 1 /\\ ( C e. RR /\\ %s ) )' % WINH)
    bcc = s([], 'simp3', 'F : ( 0 ..^ N ) --> CC')
    nn = s([t1], 'simp1d', 'N e. NN'); mm = s([t1], 'simp2d', 'M e. NN0'); vf = s([t1], 'simp3d', 'V : ( 0 ..^ N ) --> CC')
    cr = s([s([t2], 'simprd', '( C e. RR /\\ %s )' % WINH)], 'simpld', 'C e. RR')
    lam = s([s([t1, t2], 'jca', '( ( N e. NN /\\ M e. NN0 /\\ V : ( 0 ..^ N ) --> CC ) /\\ ( A. r e. ( 0 ..^ N ) ( abs ` ( V ` r ) ) <_ 1 /\\ ( C e. RR /\\ %s ) ) )' % WINH),
             w.inst('tplam')], 'syl', stmt('tplam').split(' -> ', 1)[1][:-2])
    fz = s([w.s([], 'fzofi', '( 0 ..^ N ) e. Fin')], 'a1i', '( 0 ..^ N ) e. Fin')
    # element facts under ( A0 /\ ( j /\ i ) ) etc.
    def ctx(K, has_j, has_i):
        ck = Closure(w, K, {'M': ('NN0', _cl.lift(w, mm, K)), 'C': ('RR', _cl.lift(w, cr, K))})
        return ck
    Aji = '( %s /\\ ( j e. ( 0 ..^ N ) /\\ i e. ( 0 ..^ N ) ) )' % A0
    jin = w.s([], 'simprl', '( %s -> j e. ( 0 ..^ N ) )' % Aji); iin = w.s([], 'simprr', '( %s -> i e. ( 0 ..^ N ) )' % Aji)
    cji = ctx(Aji, 1, 1)
    vj = w.s([_cl.lift(w, vf, Aji), jin], 'ffvelcdmd', '( %s -> ( V ` j ) e. CC )' % Aji)
    cji.have('( V ` j )', 'CC', vj); cji.atom('( V ` j )')
    bi = w.s([_cl.lift(w, bcc, Aji), iin], 'ffvelcdmd', '( %s -> ( F ` i ) e. CC )' % Aji)
    cji.have('( F ` i )', 'CC', bi); cji.atom('( F ` i )')
    Ajih = '( %s /\\ h e. ( 0 ..^ i ) )' % Aji
    iss = w.s([w.s([w.s([iin, w.inst('elfzofz')], 'syl', '( %s -> i e. ( 0 ... N ) )' % Aji), w.inst('elfzuz3')], 'syl', '( %s -> N e. ( ZZ>= ` i ) )' % Aji), w.inst('fzoss2')], 'syl',
              '( %s -> ( 0 ..^ i ) C_ ( 0 ..^ N ) )' % Aji)
    vh = w.s([_cl.lift(w, vf, Ajih), w.s([_cl.lift(w, iss, Ajih), w.s([], 'simpr', '( %s -> h e. ( 0 ..^ i ) )' % Ajih)], 'sseldd', '( %s -> h e. ( 0 ..^ N ) )' % Ajih)],
             'ffvelcdmd', '( %s -> ( V ` h ) e. CC )' % Ajih)
    ch = Closure(w, Ajih, {'( V ` j )': ('CC', _cl.lift(w, vj, Ajih)), '( V ` h )': ('CC', vh)}); ch.atom('( V ` j )'); ch.atom('( V ` h )')
    om = w.s([w.s([w.s([], 'fzofi', '( 0 ..^ i ) e. Fin')], 'a1i', '( %s -> ( 0 ..^ i ) e. Fin )' % Aji), ch.mem('( ( V ` j ) - ( V ` h ) )', 'CC')], 'fprodcl',
             '( %s -> %s e. CC )' % (Aji, OMJ('i')))
    cji.have(OMJ('i'), 'CC', om); cji.atom(OMJ('i'))
    VY = '( ( V ` j ) ^ ( M + 1 ) )'
    cji.have(VY, 'CC', cji.mem(VY, 'CC')); cji.atom(VY)
    TERM = '( %s x. ( ( F ` i ) x. %s ) )' % (VY, OMJ('i'))
    tc = cji.mem(TERM, 'CC')
    # per j: V^Y sum_i ( ( F ` i ) O ) = sum_i V^Y ( ( F ` i ) O )
    Aj = '( %s /\\ j e. ( 0 ..^ N ) )' % A0
    # build ( ( Aj /\\ i ) -> ... ) from Aji facts: ( ( Aj /\\ i e. X ) -> Aji )
    Aj_i = '( %s /\\ i e. ( 0 ..^ N ) )' % Aj
    cv = w.s([w.s([], 'simpll', '( %s -> %s )' % (Aj_i, A0)), w.s([w.s([], 'simplr', '( %s -> j e. ( 0 ..^ N ) )' % Aj_i), w.s([], 'simpr', '( %s -> i e. ( 0 ..^ N ) )' % Aj_i)],
                                                            'jca', '( %s -> ( j e. ( 0 ..^ N ) /\\ i e. ( 0 ..^ N ) ) )' % Aj_i)], 'jca', '( %s -> %s )' % (Aj_i, Aji))
    TO = lambda st: w.s([cv, st], 'syl', '( %s -> %s )' % (Aj_i, body_of(w, st)))
    boc = TO(cji.mem('( ( F ` i ) x. %s )' % OMJ('i'), 'CC'))
    vyj = w.s([w.s([_cl.lift(w, vf, Aj), w.s([], 'simpr', '( %s -> j e. ( 0 ..^ N ) )' % Aj)], 'ffvelcdmd', '( %s -> ( V ` j ) e. CC )' % Aj), _cl.lift(w, s([mm, w.inst('peano2nn0')], 'syl', '( M + 1 ) e. NN0'), Aj)], 'expcld', '( %s -> %s e. CC )' % (Aj, VY))
    m1 = w.s([_cl.lift(w, fz, Aj), vyj, boc], 'fsummulc2', '( %s -> ( %s x. sum_ i e. ( 0 ..^ N ) ( ( F ` i ) x. %s ) ) = sum_ i e. ( 0 ..^ N ) %s )' % (Aj, VY, OMJ('i'), TERM))
    L1 = s([m1], 'sumeq2dv', '%s = sum_ j e. ( 0 ..^ N ) sum_ i e. ( 0 ..^ N ) %s' % (LAMB, TERM))
    L2 = s([fz, fz, tc], 'fsumcom', 'sum_ j e. ( 0 ..^ N ) sum_ i e. ( 0 ..^ N ) %s = sum_ i e. ( 0 ..^ N ) sum_ j e. ( 0 ..^ N ) %s' % (TERM, TERM))
    # per i: sum_j V^Y ( ( F ` i ) O ) = ( F ` i ) sum_j ( V^Y O )
    Ai = '( %s /\\ i e. ( 0 ..^ N ) )' % A0
    Ai_j = '( %s /\\ j e. ( 0 ..^ N ) )' % Ai
    cv2 = w.s([w.s([], 'simpll', '( %s -> %s )' % (Ai_j, A0)), w.s([w.s([], 'simpr', '( %s -> j e. ( 0 ..^ N ) )' % Ai_j), w.s([], 'simplr', '( %s -> i e. ( 0 ..^ N ) )' % Ai_j)],
                                                             'jca', '( %s -> ( j e. ( 0 ..^ N ) /\\ i e. ( 0 ..^ N ) ) )' % Ai_j)], 'jca', '( %s -> %s )' % (Ai_j, Aji))
    TO2 = lambda st: w.s([cv2, st], 'syl', '( %s -> %s )' % (Ai_j, body_of(w, st)))
    r12 = TO2(ap(w, Aji, 'mul12d', '%s = ( ( F ` i ) x. ( %s x. %s ) )' % (TERM, VY, OMJ('i')), cji))
    si1 = w.s([r12], 'sumeq2dv', '( %s -> sum_ j e. ( 0 ..^ N ) %s = sum_ j e. ( 0 ..^ N ) ( ( F ` i ) x. ( %s x. %s ) ) )' % (Ai, TERM, VY, OMJ('i')))
    bI = w.s([_cl.lift(w, bcc, Ai), w.s([], 'simpr', '( %s -> i e. ( 0 ..^ N ) )' % Ai)], 'ffvelcdmd', '( %s -> ( F ` i ) e. CC )' % Ai)
    LI = 'sum_ j e. ( 0 ..^ N ) ( %s x. %s )' % (VY, OMJ('i'))
    si2 = w.s([_cl.lift(w, fz, Ai), bI, TO2(cji.mem('( %s x. %s )' % (VY, OMJ('i')), 'CC'))], 'fsummulc2',
              '( %s -> ( ( F ` i ) x. %s ) = sum_ j e. ( 0 ..^ N ) ( ( F ` i ) x. ( %s x. %s ) ) )' % (Ai, LI, VY, OMJ('i')))
    si3 = w.s([si1, si2], 'eqtr4d', '( %s -> sum_ j e. ( 0 ..^ N ) %s = ( ( F ` i ) x. %s ) )' % (Ai, TERM, LI))
    L3 = s([si3], 'sumeq2dv', 'sum_ i e. ( 0 ..^ N ) sum_ j e. ( 0 ..^ N ) %s = sum_ i e. ( 0 ..^ N ) ( ( F ` i ) x. %s )' % (TERM, LI))
    eqL = s([L1, L2, L3], '3eqtrd', '%s = sum_ i e. ( 0 ..^ N ) ( ( F ` i ) x. %s )' % (LAMB, LI))
    ci = Closure(w, Ai, {'C': ('RR', _cl.lift(w, cr, Ai)), '( F ` i )': ('CC', bI)}); ci.atom('( F ` i )')
    lic = w.s([_cl.lift(w, fz, Ai), TO2(cji.mem('( %s x. %s )' % (VY, OMJ('i')), 'CC'))], 'fsumcl', '( %s -> %s e. CC )' % (Ai, LI))
    ci.have(LI, 'CC', lic); ci.atom(LI)
    ab1 = s([fz, ci.mem('( ( F ` i ) x. %s )' % LI, 'CC')], 'fsumabs', '( abs ` sum_ i e. ( 0 ..^ N ) ( ( F ` i ) x. %s ) ) <_ sum_ i e. ( 0 ..^ N ) ( abs ` ( ( F ` i ) x. %s ) )' % (LI, LI))
    am = ap(w, Ai, 'absmuld', '( abs ` ( ( F ` i ) x. %s ) ) = ( ( abs ` ( F ` i ) ) x. ( abs ` %s ) )' % (LI, LI), ci)
    # ( abs ` LI ) <_ ( 2 ^ i ) C from tplam
    li = w.s([w.s([_cl.lift(w, lam, Ai), w.s([], 'simpr', '( %s -> i e. ( 0 ..^ N ) )' % Ai)], 'jca', '( %s -> ( %s /\\ i e. ( 0 ..^ N ) ) )' % (Ai, body_of(w, lam))), w.inst('rspa')],
             'syl', '( %s -> ( abs ` %s ) <_ ( ( 2 ^ i ) x. C ) )' % (Ai, LI))
    ci.have('i', 'NN0', w.s([w.s([], 'simpr', '( %s -> i e. ( 0 ..^ N ) )' % Ai), w.inst('elfzonn0')], 'syl', '( %s -> i e. NN0 )' % Ai))
    le = ap(w, Ai, 'lemul2ad', '( ( abs ` ( F ` i ) ) x. ( abs ` %s ) ) <_ ( ( abs ` ( F ` i ) ) x. ( ( 2 ^ i ) x. C ) )' % LI, ci, facts=[li])
    lei = w.s([am, le], 'eqbrtrd', '( %s -> ( abs ` ( ( F ` i ) x. %s ) ) <_ ( ( abs ` ( F ` i ) ) x. ( ( 2 ^ i ) x. C ) ) )' % (Ai, LI))
    ab2 = s([fz, ci.mem('( abs ` ( ( F ` i ) x. %s ) )' % LI, 'RR'), ci.mem('( ( abs ` ( F ` i ) ) x. ( ( 2 ^ i ) x. C ) )', 'RR'), lei], 'fsumle',
            'sum_ i e. ( 0 ..^ N ) ( abs ` ( ( F ` i ) x. %s ) ) <_ sum_ i e. ( 0 ..^ N ) ( ( abs ` ( F ` i ) ) x. ( ( 2 ^ i ) x. C ) )' % LI)
    tot = s([ab1, ab2], 'letrd', '( abs ` sum_ i e. ( 0 ..^ N ) ( ( F ` i ) x. %s ) ) <_ sum_ i e. ( 0 ..^ N ) ( ( abs ` ( F ` i ) ) x. ( ( 2 ^ i ) x. C ) )' % LI)
    w.qed([s([eqL], 'fveq2d', '( abs ` %s ) = ( abs ` sum_ i e. ( 0 ..^ N ) ( ( F ` i ) x. %s ) )' % (LAMB, LI)), tot], 'eqbrtrd', S['tpupp'])
    return run(w)


if __name__ == '__main__':
    gen_upp()
