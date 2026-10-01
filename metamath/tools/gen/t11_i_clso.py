"""T11: ` moveEntry ` at the machine keeping the flag only (class ` { fl = O } ` ): ` scanNext ` and ` scanF ` move an
entry between ` isZero ` and the ` load' ` that reads its flag.

  tmcmvino   the mover's read interface inside ` { h e. TMSt | ( TMfl ` h ) = O } `
  tmimeno    ~ tm2lme there
  tmimebo    its B form at the encoding of ` F < 2 ^ N `

    MM_DB=sorties/t11.mm python3 tools/gen/t11_i_clso.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t8blib import *
from t7_v_leb import enc_facts, finish
from t7b_h_dmq import rab_elim
from t7lib import rab_in
from t8b_c_me import me_inst
import t7c_b_drc as DRC

SEL = sys.argv[1:]
NO = '{ h e. TMSt | ( TMfl ` h ) = O }'
NOC = lambda t: '( TMfl ` %s ) = O' % t
Q_ = lambda txt, old: txt.replace(old, NO)
ST_MVINO = Q_(ST_MVIN, NPC)
CONCL_MENO = Q_(CONCL_MEN, NPC)
CONCL_MEBO = Q_(CONCL_MEB, NPC)
STMTS = {'tmcmvino': ST_MVINO, 'tmimeno': '( %s -> %s )' % (cj(TREE_ME), CONCL_MENO), 'tmimebo': '( %s -> %s )' % (cj(TREE_MEB), CONCL_MEBO)}


def no_out(w, ph, r, rin):
    rr, cnd = rab_elim(w, ph, NO, NOC, r, rin)
    return rr, cnd


def no_keep(w, ph, nv, N, fl):
    f = w.s([nv['fields']['fl'], fl], 'eqtrd', '( %s -> ( TMfl ` %s ) = O )' % (ph, N))
    return rab_in(w, ph, NO, NOC, N, nv['mem'], f)


def tmcmvino():
    lab = 'tmcmvino'
    w = W(lab, 'The mover\'s read interface at the concrete handlers inside the class of states with ` flag ` pinned: '
               '` readA ` touches only ` ra ` and ` da ` , so the class is preserved (~ tmcmvin with only the flag pinned).')
    ph = '( r e. %s /\\ z e. %s )' % (NO, BITS)
    rin = w.s([], 'simpl', '( %s -> r e. %s )' % (ph, NO))
    zz = w.s([], 'simpr', '( %s -> z e. %s )' % (ph, BITS))
    rr, fl = no_out(w, ph, 'r', rin)
    N = NVA('r', 'z')
    nv = rd_bit(w, ph, 'A', 'r', 'z', rr, zz)
    c1, _ = cis_val(w, ph, nv, N)
    p1 = pbr_val(w, ph, nv, N, 'z', zz)
    body1 = '( ( %s ` %s ) = 1o /\\ ( %s ` %s ) = z /\\ %s e. %s )' % (CIS, N, PBR, N, N, NO)
    j1 = w.s([c1, p1, no_keep(w, ph, nv, N, fl)], '3jca', '( %s -> %s )' % (ph, body1))
    r1 = w.s([j1], 'rgen2', 'A. r e. %s A. z e. %s %s' % (NO, BITS, body1))
    ph2 = 'r e. %s' % NO
    rr2, fl2 = no_out(w, ph2, 'r', w.s([], 'id', '( %s -> r e. %s )' % (ph2, NO)))
    N2 = NVA('r', '4')
    nv2 = rd_comma(w, ph2, 'A', 'r', rr2)
    c2, _ = cis_val(w, ph2, nv2, N2)
    n0a = w.s([w.s([w.s([], '1n0', '1o =/= (/)')], 'nesymi', '-. (/) = 1o')], 'a1i', '( %s -> -. (/) = 1o )' % ph2)
    c2n = w.s([w.s([c2], 'eqeq1d', '( %s -> ( ( %s ` %s ) = 1o <-> (/) = 1o ) )' % (ph2, CIS, N2)), n0a], 'mtbird', '( %s -> -. ( %s ` %s ) = 1o )' % (ph2, CIS, N2))
    body2 = '( -. ( %s ` %s ) = 1o /\\ %s e. %s )' % (CIS, N2, N2, NO)
    j2 = w.s([c2n, no_keep(w, ph2, nv2, N2, fl2)], 'jca', '( %s -> %s )' % (ph2, body2))
    r2 = w.s([j2], 'rgen', 'A. r e. %s %s' % (NO, body2))
    w.qed([r1, r2], 'pm3.2i', ST_MVINO)
    return w.run()


def tmimeno():
    def more(w, ps, mk, ex):
        mv = w.s([], 'tmcmvino', ST_MVINO)
        ex[ST_MVINO] = w.s([mv], 'a1i', '( %s -> %s )' % (ps, ST_MVINO))
        ss = w.s([w.s([], 'ssrab2', '%s C_ TMSt' % NO)], 'a1i', '( %s -> %s C_ TMSt )' % (ps, NO))
        ex[SSS(NO)] = w.s([ss, mk['seq']], 'sseqtrrd', '( %s -> %s C_ %s )' % (ps, NO, S))
    w, cc = me_inst('tmimeno', 'Lean\'s ` moveEntry_runs ` at the machine keeping ` flag ` : ` moveEntry src dst s ` stays in the '
                    'class of states with ` flag = O ` (~ tmcmvino ) and moves the top entry of ` src ` onto ` dst ` within '
                    '` 2 ( # W ) + 4 ` steps (~ tm2lme ).', NO, more)
    assert cc == CONCL_MENO, cc
    return w.run()


def tmimebo():
    lab = 'tmimebo'
    ph = cj(TREE_MEB)
    w = W(lab, 'Lean\'s ` moveEntry_le_B ` at the machine keeping ` flag ` : ~ tmimeno at the encoding of ` F < 2 ^ N ` , '
               'within ` ( TMB ` N ) ` steps.')
    c = Ctx(w, ph, TREE_MEB)
    phm = c[PHM]
    e = enc_facts(w, ph, 'F', c['F e. NN0'], c['N e. NN0'], c['F < ( 2 ^ N )'])
    wb = DRC.enc_bits(w, ph, e)
    ENF_ = '( encNatGam ` F )'
    t, cc = inst(w, ph, 'tmimeno', {'W': ENF_}, Bld(w, ph, c, {WRD(ENF_, BITS): wb}))
    C1, D1, n1 = triple_parts(cc)
    ln = w.s([w.s([e['gv']], 'fveq2d', '( %s -> ( # ` %s ) = ( # ` ( inclBool o. %s ) ) )' % (ph, ENF_, e['EF'])),
              w.s([e['ef'], w.inst('bwmaplen')], 'syl', '( %s -> ( # ` ( inclBool o. %s ) ) = ( # ` %s ) )' % (ph, e['EF'], e['EF']))],
             'eqtrd', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (ph, ENF_, e['EF']))
    lw = w.s([wb, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, ENF_))
    le0 = w.s([e['ef'], w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, e['EF']))
    finish(w, ph, phm, t, C1, D1, n1, c['N e. NN0'], {'( # ` %s )' % ENF_: lw, '( # ` %s )' % e['EF']: le0}, [ln, e['le']], '2')
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
