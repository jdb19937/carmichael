"""T7c: ` dropNum ` at the machine inside the class of states with a pinned
` flag ` (T7b-HANDOFF item 1: isZero's flag must survive ` dropNum s ` ).

  tmcdrin    the read interface of ` dropNum ` at the class { flag = O }
  tmcdropn   ` dropNum x ` at the machine, class { flag = O } (tm2fdropn)
  tmcdropnb  its B form ( F < 2 ^ N , ( TMB ` N ) steps)
  tmidropnb  the installed form (TMIdrop)

    MM_DB=sorties/t7c.mm python3 tools/gen/t7c_b_drc.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t7blib import *
from t7leb import TREE_DROPB, NUMS, ENF, TB
from t7_e_cmp import machine, togk, letgk, bitsgk, cis_ty
from t7_v_leb import enc_facts, finish
from t7b_h_dmq import rab_elim
from t7b_c_runs import pred_tree

SEL = sys.argv[1:]

NFO = '{ h e. TMSt | ( TMfl ` h ) = O }'
FLO = lambda h: '( TMfl ` %s ) = O' % h
ST_DRIN = ('( A. r e. %s A. z e. %s ( ( %s ` %s ) = 1o /\\ %s e. %s ) /\\ A. r e. %s ( -. ( %s ` %s ) = 1o /\\ %s e. %s ) )'
           % (NFO, BITS, CIS, NVA('r', 'z'), NVA('r', 'z'), NFO, NFO, CIS, NVA('r', '4'), NVA('r', '4'), NFO))
CONCL_DROPN = TRI(CLN('A', NFO, UP('D', 'K', WYX4)), CLN('E', NFO, UP('D', 'K', 'X')), '( ( # ` W ) + 1 )')
CONCL_DROPNB = TRI(CLN('A', NFO, UP('D', 'K', CC(ENF, YX4))), CLN('E', NFO, UP('D', 'K', 'X')), TB)


def tmcdrin():
    lab = 'tmcdrin'
    w = W(lab, 'The read interface of ` dropNum ` at the concrete handlers inside the class of states with '
               '` flag ` pinned to ` O ` : ` readA ` touches only ` ra ` and ` da ` , so the branch ` ra.isSome ` '
               'is taken on a bit, fails on the terminator ` 4 ` , and the class is preserved (the form of '
               '~ tm2fdropn ).')
    ph = '( r e. %s /\\ z e. %s )' % (NFO, BITS)
    rin = w.s([], 'simpl', '( %s -> r e. %s )' % (ph, NFO))
    zz = w.s([], 'simpr', '( %s -> z e. %s )' % (ph, BITS))
    rr, fl = rab_elim(w, ph, NFO, FLO, 'r', rin)
    N = NVA('r', 'z')
    nv = rd_bit(w, ph, 'A', 'r', 'z', rr, zz)
    c1, _ = cis_val(w, ph, nv, N)
    f1 = w.s([nv['fields']['fl'], fl], 'eqtrd', '( %s -> %s )' % (ph, FLO(N)))
    m1 = rab_in(w, ph, NFO, FLO, N, nv['mem'], f1)
    body1 = '( ( %s ` %s ) = 1o /\\ %s e. %s )' % (CIS, N, N, NFO)
    j1 = w.s([c1, m1], 'jca', '( %s -> %s )' % (ph, body1))
    r1 = w.s([j1], 'rgen2', 'A. r e. %s A. z e. %s %s' % (NFO, BITS, body1))
    ph2 = 'r e. %s' % NFO
    rin2 = w.s([], 'id', '( %s -> r e. %s )' % (ph2, NFO))
    rr2, fl2 = rab_elim(w, ph2, NFO, FLO, 'r', rin2)
    N2 = NVA('r', '4')
    nv2 = rd_comma(w, ph2, 'A', 'r', rr2)
    c2, _ = cis_val(w, ph2, nv2, N2)
    c2n = not1o(w, ph2, c2, CIS, N2)
    f2 = w.s([nv2['fields']['fl'], fl2], 'eqtrd', '( %s -> %s )' % (ph2, FLO(N2)))
    m2 = rab_in(w, ph2, NFO, FLO, N2, nv2['mem'], f2)
    body2 = '( -. ( %s ` %s ) = 1o /\\ %s e. %s )' % (CIS, N2, N2, NFO)
    j2 = w.s([c2n, m2], 'jca', '( %s -> %s )' % (ph2, body2))
    r2 = w.s([j2], 'rgen', 'A. r e. %s %s' % (NFO, body2))
    w.qed([r1, r2], 'pm3.2i', ST_DRIN)
    return w.run()


def tmcdropn():
    lab = 'tmcdropn'
    ph = cj(TREE_DROP)
    w = W(lab, '` dropNum x ` at the machine inside the class of states with ` flag ` pinned to ` O ` : '
               '~ tm2fdropn with the handler ` readA ` , the test ` ra.isSome ` , the bit letters and the terminator '
               '` 4 ` , the interface by ~ tmcdrin .  Lean: ` dropNum_runs ` ( ` flag ` is not touched).')
    c = Ctx(w, ph, TREE_DROP)
    mk = machine(w, ph, c, ['K'])
    K = mk['k']['K']
    xg = c[WRD('X', GAM)]
    g4 = closed(w, ph, 'gamma4', "4 e. Gamma'")
    x4 = w.s([w.s([g4], 's1cld', '( %s -> <" 4 "> e. Word Gamma\' )' % ph), xg, w.inst('ccatcl')], 'syl2anc',
             "( %s -> %s e. Word Gamma' )" % (ph, YX4))
    dri = w.s([], 'tmcdrin', ST_DRIN)
    HC_ = 'A. r e. %s A. z e. %s ( ( %s ` %s ) = 1o /\\ %s e. %s )' % (NFO, BITS, CIS, NVA('r', 'z'), NVA('r', 'z'), NFO)
    HE_ = 'A. r e. %s ( -. ( %s ` %s ) = 1o /\\ %s e. %s )' % (NFO, CIS, NVA('r', '4'), NVA('r', '4'), NFO)
    hc = w.s([w.s([dri], 'simpli', HC_)], 'a1i', '( %s -> %s )' % (ph, HC_))
    he = w.s([w.s([dri], 'simpri', HE_)], 'a1i', '( %s -> %s )' % (ph, HE_))
    ss = w.s([w.s([], 'ssrab2', '%s C_ TMSt' % NFO)], 'a1i', '( %s -> %s C_ TMSt )' % (ph, NFO))
    nss = w.s([ss, mk['seq']], 'sseqtrrd', '( %s -> %s C_ ( 2nd ` T ) )' % (ph, NFO))
    extra = {PHM: mk['phm'], 'T e. V': mk['tv'], MTY: mk['mt'], 'K e. %s' % DG: K['kd'], RTY('TMrdA', 'K'): K['hdl']['TMrdA'],
             CTY(CIS): cis_ty(w, ph, mk), '%s C_ %s' % (BITS, GK): bitsgk(w, ph, mk, 'K'),
             WRD(YX4, GK): togk(w, ph, mk, YX4, 'K', x4), '4 e. %s' % GK: letgk(w, ph, mk, '4', 'K', g4),
             WRD('X', GK): togk(w, ph, mk, 'X', 'K', xg), HC_: hc, HE_: he, '%s C_ ( 2nd ` T )' % NFO: nss}
    bld = Builder(w, ph, c, extra)
    m = {'F': 'TMrdA', 'C': CIS, 'B': BITS, 'Y': '4', 'N': NFO}
    ante, concl = split_imp(stmt('tm2fdropn'))
    tree = tsub(parse_conj(ante), m)
    st = bld(tree)
    c2 = tsub_text(concl, m)
    assert c2 == CONCL_DROPN, (c2, CONCL_DROPN)
    w.qed([st, w.inst('tm2fdropn')], 'syl', '( %s -> %s )' % (ph, c2))
    return w.run()


def enc_bits(w, ph, e, F='F'):
    ib = w.s([e['ef'], w.inst('tmcibw')], 'syl', '( %s -> ( inclBool o. %s ) e. Word %s )' % (ph, e['EF'], BITS))
    return w.s([e['gv'], ib], 'eqeltrd', '( %s -> ( encNatGam ` %s ) e. Word %s )' % (ph, F, BITS))


def tmcdropnb():
    lab = 'tmcdropnb'
    ph = cj(TREE_DROPB)
    w = W(lab, '` dropNum_le_B ` at the machine inside the class of states with ` flag ` pinned: ` dropNum x ` '
               'on the encoding of ` F < 2 ^ N ` in ` ( TMB ` N ) ` steps (~ tmcdropn ).')
    c = Ctx(w, ph, TREE_DROPB)
    phm = c[PHM]
    ex = {'T e. V': w.s([phm], 'simpld', '( %s -> T e. V )' % ph), MTY: w.s([phm], 'simprd', '( %s -> %s )' % (ph, MTY))}
    e = enc_facts(w, ph, 'F', c['F e. NN0'], c['N e. NN0'], c['F < ( 2 ^ N )'])
    wb = enc_bits(w, ph, e)
    ex[WRD(ENF, BITS)] = wb
    t, cc = inst(w, ph, 'tmcdropn', {'W': ENF}, Builder(w, ph, c, ex))
    C1, D1, n1 = triple_parts(cc)
    ln = w.s([w.s([e['gv']], 'fveq2d', '( %s -> ( # ` %s ) = ( # ` ( inclBool o. %s ) ) )' % (ph, ENF, e['EF'])),
              w.s([e['ef'], w.inst('bwmaplen')], 'syl', '( %s -> ( # ` ( inclBool o. %s ) ) = ( # ` %s ) )' % (ph, e['EF'], e['EF']))], 'eqtrd',
             '( %s -> ( # ` %s ) = ( # ` %s ) )' % (ph, ENF, e['EF']))
    lw = w.s([wb, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, ENF))
    le0 = w.s([e['ef'], w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, e['EF']))
    finish(w, ph, phm, t, C1, D1, n1, c['N e. NN0'], {'( # ` %s )' % ENF: lw, '( # ` %s )' % e['EF']: le0}, [ln, e['le']], '1')
    return w.run()


def STMT_IDNB():
    f = FRAGS['drop']
    return pred_tree(TREE_DROPB, f), tsub_text(CONCL_DROPNB, f.lmap())


def tmidropnb():
    lab = 'tmidropnb'
    f = FRAGS['drop']
    T, C = STMT_IDNB()
    ph = cj(T)
    w = W(lab, 'The installed form of ~ tmcdropnb : Lean\'s ` dropNum_le_B ` wherever ` dropNum x ` is installed, '
               'inside the class of states with ` flag ` pinned (the ` flag ` of a preceding ` isZero ` survives).')
    c = Ctx(w, ph, T)
    pst = c[f.pred()]
    d = w.s([], 'df-%s' % f.const.lower(), f.df())
    u = w.s([pst, d], 'sylib', '( %s -> %s )' % (ph, f.rhs()))
    cu = Ctx(w, ph, f.rhs_tree(), root=u)
    bld = Bld(w, ph, c, cu.all())
    st, c2 = inst(w, ph, 'tmcdropnb', f.lmap(), bld)
    assert c2 == C, (c2, C)
    w.lines[-1] = w.lines[-1].replace(st + ':', 'qed:', 1)
    return w.run()


STMTS = {'tmcdrin': ST_DRIN, 'tmcdropn': '( %s -> %s )' % (cj(TREE_DROP), CONCL_DROPN),
         'tmcdropnb': '( %s -> %s )' % (cj(TREE_DROPB), CONCL_DROPNB)}
_T, _C = STMT_IDNB()
STMTS['tmidropnb'] = '( %s -> %s )' % (cj(_T), _C)

if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
