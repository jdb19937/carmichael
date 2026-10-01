"""T8b: moveEntry at the machine on its installation predicate TMIme.

  tmime    moveEntry_runs at the class ( 2nd ` T ) (~ tm2lme at readA / isSome / bit push, ~ tmclhi )
  tmimen   moveEntry_runs verbatim: flag, cmp, carry kept (class NP( O , Q , R ), ~ tmcmvin )
  tmimeb   moveEntry_le_B (~ tmimen at the encoding of F < 2 ^ N )

    MM_DB=sorties/t8b.mm python3 tools/gen/t8b_c_me.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t8blib import *
from t7_v_leb import enc_facts, enc_bits, finish

SEL = sys.argv[1:]
K3_ = ['K', 'J', 'I']


def me_inst(lab, desc, N, more=None):
    T = TREE_ME
    ps = cj(T)
    w = W(lab, desc)
    c, mk, ne, base = setup(w, ps, T, K3_, pred=FRAGS['me'].pred(), fname='me')
    ex = dict(base)
    ex.update(H.handler_extra(w, ps, mk, H.IFACE))
    m = H.hm('tm2lme'); m.update(FRAGS['me'].lmap()); m['N'] = N
    if more:
        more(w, ps, mk, ex)
    t, cc = inst(w, ps, 'tm2lme', m, Bld(w, ps, c, ex))
    w.lines[-1] = 'qed:' + w.lines[-1].split(':', 1)[1]
    return w, cc


def tmime():
    w, cc = me_inst('tmime', 'Lean\'s ` moveEntry_runs ` at the machine, from any state: wherever ` moveEntry src dst s ` '
                    'is installed, the top entry ` W ` of ` src ` moves onto ` dst ` , every other stack kept, within '
                    '` 2 ( # W ) + 4 ` steps (~ tm2lme at the concrete handlers, ~ tmclhi ).', S)
    assert cc == CONCL_ME, cc
    return w.run()


def tmimen():
    def more(w, ps, mk, ex):
        mv = w.s([], 'tmcmvin', ST_MVIN)
        ex[ST_MVIN] = w.s([mv], 'a1i', '( %s -> %s )' % (ps, ST_MVIN))
        ss = w.s([w.s([], 'ssrab2', '%s C_ TMSt' % NPC)], 'a1i', '( %s -> %s C_ TMSt )' % (ps, NPC))
        ex[SSS(NPC)] = w.s([ss, mk['seq']], 'sseqtrrd', '( %s -> %s C_ %s )' % (ps, NPC, S))
    ps = cj(TREE_ME)
    w, cc = me_inst('tmimen', 'Lean\'s ` moveEntry_runs ` at the machine verbatim: ` moveEntry src dst s ` keeps '
                    '` flag ` , ` cmp ` and ` carry ` (the class ` NP( O , Q , R ) ` , ~ tmcmvin ) and moves the top '
                    'entry of ` src ` onto ` dst ` within ` 2 ( # W ) + 4 ` steps (~ tm2lme ).', NPC, more)
    assert cc == CONCL_MEN, cc
    return w.run()


def tmimeb():
    lab = 'tmimeb'
    ph = cj(TREE_MEB)
    w = W(lab, 'Lean\'s ` moveEntry_le_B ` at the machine: ~ tmimen at the encoding of ` F < 2 ^ N ` , within '
               '` ( TMB ` N ) ` steps.')
    c = Ctx(w, ph, TREE_MEB)
    phm = c[PHM]
    e = enc_facts(w, ph, 'F', c['F e. NN0'], c['N e. NN0'], c['F < ( 2 ^ N )'])
    wb = enc_bits(w, ph, e)
    ENF_ = '( encNatGam ` F )'
    t, cc = inst(w, ph, 'tmimen', {'W': ENF_}, Bld(w, ph, c, {WRD(ENF_, BITS): wb}))
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
