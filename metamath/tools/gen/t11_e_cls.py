"""T11: class-keeping variants at the class NQ of states with ` flag ` pinned to ` O ` and
` cmp ` pinned to ` Q ` (the carry free), and the installed generic-word dropNum.

  tmcmvinq    the mover's read interface inside NQ (~ tmcmvin at NQ)
  tmimenq     moveEntry_runs keeping NQ (~ tmimen at NQ)
  tmimebq     its B form (~ tmimeb at NQ)
  tmcdrinq    dropNum's read interface inside NQ (~ tmcdrin at NQ)
  tmcdropnq   dropNum x at the machine inside NQ (~ tmcdropn at NQ)
  tmcdropnbq  its B form (~ tmcdropnb at NQ)
  tmidropnbq  the installed form (~ tmidropnb at NQ)
  tmidropnw   the installed form of ~ tmcdropn (class { flag = O }, generic bit word W)
  tmrdbrorq   the peek handler readBraOr keeps cmp

    MM_DB=sorties/t11.mm MM_HEAP=16g python3 tools/gen/t11_e_cls.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t8blib import *
from t7leb import TREE_DROPB, ENF
from t7_e_cmp import machine, togk, letgk, bitsgk, cis_ty
from t7_v_leb import enc_facts, finish
from t7b_h_dmq import rab_elim
from t7b_c_runs import pred_tree
from t7lib import tuple_facts, st_comps, _transport, rab_in
from t10lib import RBO, OPT, ORDER, FLD, MK
from t8b_c_me import me_inst
import t7c_b_drc as DRC

SEL = sys.argv[1:]

NQ = '{ h e. TMSt | ( ( TMfl ` h ) = O /\\ ( TMcmp ` h ) = Q ) }'
NQCOND = lambda t: '( ( TMfl ` %s ) = O /\\ ( TMcmp ` %s ) = Q )' % (t, t)
Q_ = lambda txt, old: txt.replace(old, NQ)

ST_MVINQ = Q_(ST_MVIN, NPC)
CONCL_MENQ = Q_(CONCL_MEN, NPC)
CONCL_MEBQ = Q_(CONCL_MEB, NPC)
ST_DRINQ = Q_(DRC.ST_DRIN, DRC.NFO)
CONCL_DROPNQ = Q_(DRC.CONCL_DROPN, DRC.NFO)
CONCL_DROPNBQ = Q_(DRC.CONCL_DROPNB, DRC.NFO)
ST_RBOQ = '( ( V e. TMSt /\\ O e. %s ) -> ( TMcmp ` ( %s ` <. V , O >. ) ) = ( TMcmp ` V ) )' % (OPT, RBO)
for _t, _o in [(ST_MVINQ, NPC), (CONCL_MENQ, NPC), (CONCL_MEBQ, NPC), (ST_DRINQ, DRC.NFO), (CONCL_DROPNQ, DRC.NFO),
               (CONCL_DROPNBQ, DRC.NFO)]:
    assert NQ in _t and _o not in _t


def nq_out(w, ph, r, rin):
    """from rin : ( ph -> r e. NQ ) : (r e. TMSt, fl = O, cmp = Q)"""
    rr, cnd = rab_elim(w, ph, NQ, NQCOND, r, rin)
    fl = w.s([cnd], 'simpld', '( %s -> ( TMfl ` %s ) = O )' % (ph, r))
    cm = w.s([cnd], 'simprd', '( %s -> ( TMcmp ` %s ) = Q )' % (ph, r))
    return rr, fl, cm


def nq_keep(w, ph, nv, N, fl, cm):
    """( ph -> N e. NQ ) for a reader value nv whose flag and cmp are the state's"""
    f = w.s([nv['fields']['fl'], fl], 'eqtrd', '( %s -> ( TMfl ` %s ) = O )' % (ph, N))
    c = w.s([nv['fields']['cmp'], cm], 'eqtrd', '( %s -> ( TMcmp ` %s ) = Q )' % (ph, N))
    j = w.s([f, c], 'jca', '( %s -> %s )' % (ph, NQCOND(N)))
    return rab_in(w, ph, NQ, NQCOND, N, nv['mem'], j)


# ------------------------------------------------------------ the mover
def tmcmvinq():
    lab = 'tmcmvinq'
    w = W(lab, 'The mover\'s read interface at the concrete handlers inside a class of states with ` flag ` and '
               '` cmp ` pinned (the carry free): ` readA ` touches only ` ra ` and ` da ` , so the class is preserved '
               '(~ tmcmvin with the carry unpinned).')
    ph = '( r e. %s /\\ z e. %s )' % (NQ, BITS)
    rin = w.s([], 'simpl', '( %s -> r e. %s )' % (ph, NQ))
    zz = w.s([], 'simpr', '( %s -> z e. %s )' % (ph, BITS))
    rr, fl, cm = nq_out(w, ph, 'r', rin)
    N = NVA('r', 'z')
    nv = rd_bit(w, ph, 'A', 'r', 'z', rr, zz)
    c1, _ = cis_val(w, ph, nv, N)
    p1 = pbr_val(w, ph, nv, N, 'z', zz)
    ptxt = '( %s ` %s ) = z' % (PBR, N)
    ctxt = '( %s ` %s ) = 1o' % (CIS, N)
    m1 = nq_keep(w, ph, nv, N, fl, cm)
    body1 = '( %s /\\ %s /\\ %s e. %s )' % (ctxt, ptxt, N, NQ)
    j1 = w.s([c1, p1, m1], '3jca', '( %s -> %s )' % (ph, body1))
    r1 = w.s([j1], 'rgen2', 'A. r e. %s A. z e. %s %s' % (NQ, BITS, body1))
    ph2 = 'r e. %s' % NQ
    rin2 = w.s([], 'id', '( %s -> r e. %s )' % (ph2, NQ))
    rr2, fl2, cm2 = nq_out(w, ph2, 'r', rin2)
    N2 = NVA('r', '4')
    nv2 = rd_comma(w, ph2, 'A', 'r', rr2)
    c2, _ = cis_val(w, ph2, nv2, N2)
    n0 = w.s([], '1n0', '1o =/= (/)')
    n0b = w.s([n0], 'nesymi', '-. (/) = 1o')
    n0a = w.s([n0b], 'a1i', '( %s -> -. (/) = 1o )' % ph2)
    e2 = w.s([c2], 'eqeq1d', '( %s -> ( ( %s ` %s ) = 1o <-> (/) = 1o ) )' % (ph2, CIS, N2))
    c2n = w.s([e2, n0a], 'mtbird', '( %s -> -. ( %s ` %s ) = 1o )' % (ph2, CIS, N2))
    m2 = nq_keep(w, ph2, nv2, N2, fl2, cm2)
    body2 = '( -. ( %s ` %s ) = 1o /\\ %s e. %s )' % (CIS, N2, N2, NQ)
    j2 = w.s([c2n, m2], 'jca', '( %s -> %s )' % (ph2, body2))
    r2 = w.s([j2], 'rgen', 'A. r e. %s %s' % (NQ, body2))
    w.qed([r1, r2], 'pm3.2i', ST_MVINQ)
    return w.run()


# ------------------------------------------------------------ moveEntry
def tmimenq():
    def more(w, ps, mk, ex):
        mv = w.s([], 'tmcmvinq', ST_MVINQ)
        ex[ST_MVINQ] = w.s([mv], 'a1i', '( %s -> %s )' % (ps, ST_MVINQ))
        ss = w.s([w.s([], 'ssrab2', '%s C_ TMSt' % NQ)], 'a1i', '( %s -> %s C_ TMSt )' % (ps, NQ))
        ex[SSS(NQ)] = w.s([ss, mk['seq']], 'sseqtrrd', '( %s -> %s C_ %s )' % (ps, NQ, S))
    w, cc = me_inst('tmimenq', 'Lean\'s ` moveEntry_runs ` at the machine keeping ` flag ` and ` cmp ` : '
                    '` moveEntry src dst s ` stays in the class of states with ` flag = O ` and ` cmp = Q ` '
                    '(~ tmcmvinq ) and moves the top entry of ` src ` onto ` dst ` within ` 2 ( # W ) + 4 ` steps '
                    '(~ tm2lme ).', NQ, more)
    assert cc == CONCL_MENQ, cc
    return w.run()


def tmimebq():
    lab = 'tmimebq'
    ph = cj(TREE_MEB)
    w = W(lab, 'Lean\'s ` moveEntry_le_B ` at the machine keeping ` flag ` and ` cmp ` : ~ tmimenq at the encoding '
               'of ` F < 2 ^ N ` , within ` ( TMB ` N ) ` steps.')
    c = Ctx(w, ph, TREE_MEB)
    phm = c[PHM]
    e = enc_facts(w, ph, 'F', c['F e. NN0'], c['N e. NN0'], c['F < ( 2 ^ N )'])
    wb = DRC.enc_bits(w, ph, e)
    ENF_ = '( encNatGam ` F )'
    t, cc = inst(w, ph, 'tmimenq', {'W': ENF_}, Bld(w, ph, c, {WRD(ENF_, BITS): wb}))
    C1, D1, n1 = triple_parts(cc)
    ln = w.s([w.s([e['gv']], 'fveq2d', '( %s -> ( # ` %s ) = ( # ` ( inclBool o. %s ) ) )' % (ph, ENF_, e['EF'])),
              w.s([e['ef'], w.inst('bwmaplen')], 'syl', '( %s -> ( # ` ( inclBool o. %s ) ) = ( # ` %s ) )' % (ph, e['EF'], e['EF']))],
             'eqtrd', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (ph, ENF_, e['EF']))
    lw = w.s([wb, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, ENF_))
    le0 = w.s([e['ef'], w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, e['EF']))
    finish(w, ph, phm, t, C1, D1, n1, c['N e. NN0'], {'( # ` %s )' % ENF_: lw, '( # ` %s )' % e['EF']: le0}, [ln, e['le']], '2')
    return w.run()


# ------------------------------------------------------------ dropNum
def tmcdrinq():
    lab = 'tmcdrinq'
    w = W(lab, 'The read interface of ` dropNum ` at the concrete handlers inside the class of states with '
               '` flag ` pinned to ` O ` and ` cmp ` pinned to ` Q ` : the branch ` ra.isSome ` is taken on a bit, '
               'fails on the terminator ` 4 ` , and the class is preserved (~ tmcdrin at the two-field class).')
    ph = '( r e. %s /\\ z e. %s )' % (NQ, BITS)
    rin = w.s([], 'simpl', '( %s -> r e. %s )' % (ph, NQ))
    zz = w.s([], 'simpr', '( %s -> z e. %s )' % (ph, BITS))
    rr, fl, cm = nq_out(w, ph, 'r', rin)
    N = NVA('r', 'z')
    nv = rd_bit(w, ph, 'A', 'r', 'z', rr, zz)
    c1, _ = cis_val(w, ph, nv, N)
    m1 = nq_keep(w, ph, nv, N, fl, cm)
    body1 = '( ( %s ` %s ) = 1o /\\ %s e. %s )' % (CIS, N, N, NQ)
    j1 = w.s([c1, m1], 'jca', '( %s -> %s )' % (ph, body1))
    r1 = w.s([j1], 'rgen2', 'A. r e. %s A. z e. %s %s' % (NQ, BITS, body1))
    ph2 = 'r e. %s' % NQ
    rin2 = w.s([], 'id', '( %s -> r e. %s )' % (ph2, NQ))
    rr2, fl2, cm2 = nq_out(w, ph2, 'r', rin2)
    N2 = NVA('r', '4')
    nv2 = rd_comma(w, ph2, 'A', 'r', rr2)
    c2, _ = cis_val(w, ph2, nv2, N2)
    c2n = not1o(w, ph2, c2, CIS, N2)
    m2 = nq_keep(w, ph2, nv2, N2, fl2, cm2)
    body2 = '( -. ( %s ` %s ) = 1o /\\ %s e. %s )' % (CIS, N2, N2, NQ)
    j2 = w.s([c2n, m2], 'jca', '( %s -> %s )' % (ph2, body2))
    r2 = w.s([j2], 'rgen', 'A. r e. %s %s' % (NQ, body2))
    w.qed([r1, r2], 'pm3.2i', ST_DRINQ)
    return w.run()


def tmcdropnq():
    lab = 'tmcdropnq'
    ph = cj(TREE_DROP)
    w = W(lab, '` dropNum x ` at the machine inside the class of states with ` flag ` pinned to ` O ` and ` cmp ` '
               'pinned to ` Q ` : ~ tm2fdropn with the handler ` readA ` , the test ` ra.isSome ` , the bit letters '
               'and the terminator ` 4 ` , the interface by ~ tmcdrinq .')
    c = Ctx(w, ph, TREE_DROP)
    mk = machine(w, ph, c, ['K'])
    K = mk['k']['K']
    xg = c[WRD('X', GAM)]
    g4 = closed(w, ph, 'gamma4', "4 e. Gamma'")
    x4 = w.s([w.s([g4], 's1cld', '( %s -> <" 4 "> e. Word Gamma\' )' % ph), xg, w.inst('ccatcl')], 'syl2anc',
             "( %s -> %s e. Word Gamma' )" % (ph, YX4))
    dri = w.s([], 'tmcdrinq', ST_DRINQ)
    HC_ = 'A. r e. %s A. z e. %s ( ( %s ` %s ) = 1o /\\ %s e. %s )' % (NQ, BITS, CIS, NVA('r', 'z'), NVA('r', 'z'), NQ)
    HE_ = 'A. r e. %s ( -. ( %s ` %s ) = 1o /\\ %s e. %s )' % (NQ, CIS, NVA('r', '4'), NVA('r', '4'), NQ)
    hc = w.s([w.s([dri], 'simpli', HC_)], 'a1i', '( %s -> %s )' % (ph, HC_))
    he = w.s([w.s([dri], 'simpri', HE_)], 'a1i', '( %s -> %s )' % (ph, HE_))
    ss = w.s([w.s([], 'ssrab2', '%s C_ TMSt' % NQ)], 'a1i', '( %s -> %s C_ TMSt )' % (ph, NQ))
    nss = w.s([ss, mk['seq']], 'sseqtrrd', '( %s -> %s C_ ( 2nd ` T ) )' % (ph, NQ))
    extra = {PHM: mk['phm'], 'T e. V': mk['tv'], MTY: mk['mt'], 'K e. %s' % DG: K['kd'], RTY('TMrdA', 'K'): K['hdl']['TMrdA'],
             CTY(CIS): cis_ty(w, ph, mk), '%s C_ %s' % (BITS, GK): bitsgk(w, ph, mk, 'K'),
             WRD(YX4, GK): togk(w, ph, mk, YX4, 'K', x4), '4 e. %s' % GK: letgk(w, ph, mk, '4', 'K', g4),
             WRD('X', GK): togk(w, ph, mk, 'X', 'K', xg), HC_: hc, HE_: he, '%s C_ ( 2nd ` T )' % NQ: nss}
    bld = Builder(w, ph, c, extra)
    m = {'F': 'TMrdA', 'C': CIS, 'B': BITS, 'Y': '4', 'N': NQ}
    ante, concl_ = split_imp(stmt('tm2fdropn'))
    tree = tsub(parse_conj(ante), m)
    st = bld(tree)
    c2 = tsub_text(concl_, m)
    assert c2 == CONCL_DROPNQ, (c2, CONCL_DROPNQ)
    w.qed([st, w.inst('tm2fdropn')], 'syl', '( %s -> %s )' % (ph, c2))
    return w.run()


def tmcdropnbq():
    lab = 'tmcdropnbq'
    ph = cj(TREE_DROPB)
    w = W(lab, '` dropNum_le_B ` at the machine inside the class of states with ` flag ` and ` cmp ` pinned: '
               '` dropNum x ` on the encoding of ` F < 2 ^ N ` in ` ( TMB ` N ) ` steps (~ tmcdropnq ).')
    c = Ctx(w, ph, TREE_DROPB)
    phm = c[PHM]
    ex = {'T e. V': w.s([phm], 'simpld', '( %s -> T e. V )' % ph), MTY: w.s([phm], 'simprd', '( %s -> %s )' % (ph, MTY))}
    e = enc_facts(w, ph, 'F', c['F e. NN0'], c['N e. NN0'], c['F < ( 2 ^ N )'])
    wb = DRC.enc_bits(w, ph, e)
    ex[WRD(ENF, BITS)] = wb
    t, cc = inst(w, ph, 'tmcdropnq', {'W': ENF}, Builder(w, ph, c, ex))
    C1, D1, n1 = triple_parts(cc)
    ln = w.s([w.s([e['gv']], 'fveq2d', '( %s -> ( # ` %s ) = ( # ` ( inclBool o. %s ) ) )' % (ph, ENF, e['EF'])),
              w.s([e['ef'], w.inst('bwmaplen')], 'syl', '( %s -> ( # ` ( inclBool o. %s ) ) = ( # ` %s ) )' % (ph, e['EF'], e['EF']))], 'eqtrd',
             '( %s -> ( # ` %s ) = ( # ` %s ) )' % (ph, ENF, e['EF']))
    lw = w.s([wb, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, ENF))
    le0 = w.s([e['ef'], w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, e['EF']))
    finish(w, ph, phm, t, C1, D1, n1, c['N e. NN0'], {'( # ` %s )' % ENF: lw, '( # ` %s )' % e['EF']: le0}, [ln, e['le']], '1')
    return w.run()


def STMT_IDNBQ():
    f = FRAGS['drop']
    return pred_tree(TREE_DROPB, f), tsub_text(CONCL_DROPNBQ, f.lmap())


def STMT_IDNW():
    f = FRAGS['drop']
    return pred_tree(TREE_DROP, f), tsub_text(DRC.CONCL_DROPN, f.lmap())


def installed(lab, desc, TC, src):
    f = FRAGS['drop']
    T, C = TC()
    ph = cj(T)
    w = W(lab, desc)
    c = Ctx(w, ph, T)
    pst = c[f.pred()]
    d = w.s([], 'df-%s' % f.const.lower(), f.df())
    u = w.s([pst, d], 'sylib', '( %s -> %s )' % (ph, f.rhs()))
    cu = Ctx(w, ph, f.rhs_tree(), root=u)
    bld = Bld(w, ph, c, cu.all())
    st, c2 = inst(w, ph, src, f.lmap(), bld)
    assert c2 == C, (c2, C)
    w.lines[-1] = w.lines[-1].replace(st + ':', 'qed:', 1)
    return w.run()


def tmidropnbq():
    return installed('tmidropnbq', 'The installed form of ~ tmcdropnbq : Lean\'s ` dropNum_le_B ` wherever '
                     '` dropNum x ` is installed, inside the class of states with ` flag ` and ` cmp ` pinned.',
                     STMT_IDNBQ, 'tmcdropnbq')


def tmidropnw():
    return installed('tmidropnw', 'The installed form of ~ tmcdropn : Lean\'s ` dropNum_runs ` on a bit word ` W ` '
                     'wherever ` dropNum x ` is installed, inside the class of states with ` flag ` pinned to ` O ` .',
                     STMT_IDNW, 'tmcdropn')


# ------------------------------------------------------------ readBraOr keeps cmp
def tmrdbrorq():
    lab = 'tmrdbrorq'
    w = W(lab, 'The peek handler ` readBraOr ` keeps ` cmp ` (it writes only the flag).')
    s = w.s
    ph = '( V e. TMSt /\\ O e. %s )' % OPT
    vv = s([], 'simpl', '( %s -> V e. TMSt )' % ph)
    N = '( %s ` <. V , O >. )' % RBO
    IFO = 'if ( ( ( TMfl ` V ) = 1o \\/ O = ( inl ` 2 ) ) , 1o , (/) )'
    comps = [FLD(f, 'V') for f in ORDER[:6]] + [IFO]
    val = s([], 'tmrdbrorv', '( %s -> %s = %s )' % (ph, N, MK(*comps)))
    cl = st_comps(w, ph, 'V', vv)
    ic = s([s([s([], '1oel2o', '1o e. 2o'), s([], '0el2o', '(/) e. 2o')], 'ifcli', '%s e. 2o' % IFO)], 'a1i',
           '( %s -> %s e. 2o )' % (ph, IFO))
    cls = [cl[f] for f in ORDER[:6]] + [ic]
    mem, vals = tuple_facts(w, ph, comps, cls)
    e = s([val], 'fveq2d', '( %s -> ( TMcmp ` %s ) = ( TMcmp ` %s ) )' % (ph, N, MK(*comps)))
    w.qed([e, vals['cmp']], 'eqtrd', ST_RBOQ)
    return w.run()


STMTS = {'tmcmvinq': ST_MVINQ,
         'tmimenq': '( %s -> %s )' % (cj(TREE_ME), CONCL_MENQ),
         'tmimebq': '( %s -> %s )' % (cj(TREE_MEB), CONCL_MEBQ),
         'tmcdrinq': ST_DRINQ,
         'tmcdropnq': '( %s -> %s )' % (cj(TREE_DROP), CONCL_DROPNQ),
         'tmcdropnbq': '( %s -> %s )' % (cj(TREE_DROPB), CONCL_DROPNBQ),
         'tmrdbrorq': ST_RBOQ}
_T, _C = STMT_IDNBQ()
STMTS['tmidropnbq'] = '( %s -> %s )' % (cj(_T), _C)
_T, _C = STMT_IDNW()
STMTS['tmidropnw'] = '( %s -> %s )' % (cj(_T), _C)
ORDER11E = ['tmcmvinq', 'tmimenq', 'tmimebq', 'tmcdrinq', 'tmcdropnq', 'tmcdropnbq', 'tmidropnbq', 'tmidropnw', 'tmrdbrorq']

if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
