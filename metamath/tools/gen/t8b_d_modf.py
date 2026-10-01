"""T8b: modFrag at the machine (Lean ` modFrag_runs ` at canonical inputs) on TMImodf.

  tmimodfr  the R-form: ~ tmidmr at any number R of doublings with divSteps' properties, then
            ` dropNum q ` (~ tmidrop )
  tmimodf   ~ tmimodfr at R := divSteps (~ tmidvs , ~ tmidvsle )

    MM_DB=sorties/t8b.mm python3 tools/gen/t8b_d_modf.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t8blib import *
from cl import Closure
from lin import linarith, lineq, nlinarith
from t7_e_cmp import machine
from t7b_j_dmc import XR_, HR_
from t7b_f_nat import RD, ST_DVS, ST_DVSLE
from t7b_k_dmb import RHYP
from t7blib import NF, NG, PDF as PDF7

SEL = sys.argv[1:]
assert NF == NFE and NG == NGE
TREE_R = TREE(K6, 'modf', (DATA_MODF, RHYP))
ST_R = '( %s -> %s )' % (cj(TREE_R), CONCL_MODF)


def tmimodfr():
    ph = cj(TREE_R)
    w = W('tmimodfr', 'Lean\'s ` modFrag_runs ` at the machine at canonical inputs with ` R ` any number of doublings '
                      'with ` divSteps ` \'s properties: ` divmod ` (~ tmidmr ), then ` dropNum q ` (~ tmidrop ).')
    c = Ctx(w, ph, TREE_R)
    mk = machine(w, ph, c, K6)
    phm, tv = mk['phm'], mk['tv']
    kk = mk['k']
    ne = ne_fn(w, ph, c, set(flat(dist_tree(K6))))
    dd = c[STKD('D')]
    un = unfold_all(w, ph, c[FRAGS['modf'].pred()], 'modf', K6, 'P', 'E', rec=False)
    Pdm, Edm = PL('P', 0), PL(PL('P', 1), 0)
    ex = {PHM: phm, 'T e. V': tv, MTY: mk['mt']}
    ex.update(un)
    for s_ in K6:
        ex['%s e. %s' % (s_, DG)] = kk[s_]['kd']
    for i_, a_ in enumerate(K6):
        for b_ in K6[i_ + 1:]:
            ex['%s =/= %s' % (a_, b_)] = ne(a_, b_)
            ex['%s =/= %s' % (b_, a_)] = ne(b_, a_)
    fn_, gn, nn = c['F e. NN0'], c['G e. NN'], c['N e. NN0']
    gn0 = w.s([gn, w.inst('nnnn0')], 'syl', '( %s -> G e. NN0 )' % ph)
    ef = w.s([fn_, w.inst('encnatcl')], 'syl', '( %s -> ( encodeNat ` F ) e. Word 2o )' % ph)
    eg = w.s([gn0, w.inst('encnatcl')], 'syl', '( %s -> ( encodeNat ` G ) e. Word 2o )' % ph)
    nfn = w.s([ef, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, NF))
    ngn = w.s([eg, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, NG))
    rdn, rdle = c['R e. NN0'], c['R <_ %s' % NF]
    PDFR = PDF7
    ex['%s = %s' % (PDFR, PDFR)] = w.s([], 'eqidd', '( %s -> %s = %s )' % (ph, PDFR, PDFR))
    t1, c1 = inst(w, ph, 'tmidmr', {'P': Pdm, 'E': Edm, 'R': 'R', "P'": PDFR}, Bld(w, ph, c, ex))
    Ca, Da, n1 = triple_parts(c1)
    XR, HR = XR_, HR_
    D2 = UP(UP(UP('D', 'K', XR), 'I', HR), 'J', 'Y')
    assert Da == CLN(Edm, SS, D2), Da
    cl = Closure(w, ph, {'F': ('NN0', fn_), 'G': ('NN', gn), 'N': ('NN0', nn), 'R': ('NN0', rdn)})
    cl.leaf(NF, 'NN0', nfn); cl.leaf(NG, 'NN0', ngn)
    md = '( F mod G )'; fq = '( |_ ` ( F / G ) )'
    mdn = w.s([cl.mem('F', 'ZZ'), gn, w.inst('zmodcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, md))
    fqn = w.s([fn_, gn, w.inst('fldivnn0')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, fq))
    XB = '( %s bwrd %s )' % (md, NF)
    QB = '( %s bwrd R )' % fq
    xbw = w.s([w.s([mdn], 'nn0zd', '( %s -> %s e. ZZ )' % (ph, md)), nfn, w.inst('bwrdcl')], 'syl2anc', '( %s -> %s e. Word 2o )' % (ph, XB))
    qbw = w.s([w.s([fqn], 'nn0zd', '( %s -> %s e. ZZ )' % (ph, fq)), rdn, w.inst('bwrdcl')], 'syl2anc', '( %s -> %s e. Word 2o )' % (ph, QB))
    togk = lambda X, s_, g: w.s([g, kk[s_]['wge']], 'eleqtrrd', '( %s -> %s e. Word %s )' % (ph, X, GX(s_)))
    dIg = w.s([stkfv(w, ph, 'D', 'I', tv, dd, kk['I']['kd']), kk['I']['wge']], 'eleqtrd', "( %s -> ( D ` I ) e. Word Gamma' )" % ph)
    xrg = wgcat(w, ph, '( inclBool o. %s )' % XB, YXt('X'), wib(w, ph, XB, xbw), wg4(w, ph, 'X', c[WRD('X', GAM)]))
    hrg = wgcat(w, ph, '( inclBool o. %s )' % QB, YXt('( D ` I )'), wib(w, ph, QB, qbw), wg4(w, ph, '( D ` I )', dIg))
    Wq = '( inclBool o. %s )' % QB
    wqb = w.s([qbw, w.inst('tmcibw')], 'syl', '( %s -> %s e. Word %s )' % (ph, Wq, BITS))
    SA = Stacks(w, ph, mk, 'D', dd, ne, {}).upd('K', XR, xrg)
    SB = SA.upd('J', 'Y', c[WRD('Y', GAM)])
    e2 = upc(w, ph, SA.D, 'I', HR, 'J', 'Y', tv, SA.memb, ne('I', 'J'), kk['I']['kd'], togk(HR, 'I', hrg), kk['J']['kd'], togk('Y', 'J', c[WRD('Y', GAM)]))
    DP = UP(SB.D, 'I', HR)
    t1b, Ca, Da2, n1 = hrrw(w, ph, t1, Ca, Da, n1, deq=clneq(w, ph, Edm, SS, e2, D2, DP))
    m = {'K': 'I', 'P': PL('P', 1), 'E': 'E', 'W': Wq, 'X': '( D ` I )', 'D': SB.D}
    exx = dict(ex); exx.update({WRD(Wq, BITS): wqb, STKD(SB.D): SB.memb, WRD('( D ` I )', GAM): dIg})
    t2, c2 = inst(w, ph, 'tmidrop', m, Bld(w, ph, c, exx))
    C2, D2b, n2 = triple_parts(c2)
    assert C2 == Da2, (C2, Da2)
    t = hrseq(w, ph, phm, t1b, t2, Ca, Da2, D2b, n1, n2)
    n_ = '( %s + %s )' % (n1, n2)
    chain = [('K', XR), ('J', 'Y'), ('I', '( D ` I )')]
    st, out = stk_normalize(w, ph, mk, 'D', dd, ne, chain, {XR: xrg, 'Y': c[WRD('Y', GAM)], '( D ` I )': dIg}, ['K', 'J'])
    assert chain_text('D', out) == DFIN_MODF, chain_text('D', out)
    t, C_, D_, n_ = hrrw(w, ph, t, Ca, D2b, n_, deq=clneq(w, ph, 'E', SS, st, chain_text('D', chain), DFIN_MODF))
    # the bound
    LQ = '( # ` %s )' % Wq
    lq = w.s([w.s([qbw, w.inst('bwmaplen')], 'syl', '( %s -> %s = ( # ` %s ) )' % (ph, LQ, QB)),
              w.s([w.s([fqn], 'nn0zd', '( %s -> %s e. ZZ )' % (ph, fq)), rdn, w.inst('bwrdlen')], 'syl2anc', '( %s -> ( # ` %s ) = R )' % (ph, QB))],
             'eqtrd', '( %s -> %s = R )' % (ph, LQ))
    cl.leaf(LQ, 'NN0', w.s([wqb, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, LQ)))
    pr = w.s([cl.ge0(NF), cl.ge0(NG), cl.mem(NF, 'RR'), cl.mem(NG, 'RR')], 'mulge0d' if False else 'id', '') if False else None
    le = nlinarith(w, ph, [lq, rdle, cl.ge0(NF), cl.ge0(NG)], '%s <_ %s' % (n_, MODB), closure=cl, atoms=[NF, NG, LQ, 'R'])
    hrle(w, ph, phm, t, C_, D_, n_, MODB, cl.mem(MODB, 'NN0'), le, qed=True)
    return w.run()


def tmimodf():
    ph = cj(TREE_MODF)
    w = W('tmimodf', 'Lean\'s ` modFrag_runs ` at the machine at canonical inputs: wherever ` modFrag x y q j s t ` is '
                     'installed, with ` F ` on ` x ` and ` G ` ( ` 1 <_ G ` ) on ` y ` , both below ` 2 ^ N ` , ` x ` gets '
                     '` F mod G ` as a bit word of the length of ` encodeNat F ` , ` y ` loses ` G ` , every other stack is '
                     'restored, within Lean\'s bound (~ tmimodfr at ` divSteps ` , ~ tmidvs ).')
    c = Ctx(w, ph, TREE_MODF)
    fn_, gn = c['F e. NN0'], c['G e. NN']
    ef = w.s([fn_, w.inst('encnatcl')], 'syl', '( %s -> ( encodeNat ` F ) e. Word 2o )' % ph)
    nfn = w.s([ef, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, NF))
    tln = w.s([ef, w.inst('tonatlt')], 'syl', '( %s -> ( toNat ` ( encodeNat ` F ) ) < ( 2 ^ %s ) )' % (ph, NF))
    tfe = w.s([fn_, w.inst('tonatencnat')], 'syl', '( %s -> ( toNat ` ( encodeNat ` F ) ) = F )' % ph)
    fl2n = w.s([tfe, tln], 'eqbrtrrd', '( %s -> F < ( 2 ^ %s ) )' % (ph, NF))
    fg = w.s([fn_, gn], 'jca', '( %s -> ( F e. NN0 /\\ G e. NN ) )' % ph)
    dvs = w.s([fg, w.inst('tmidvs')], 'syl', '( %s -> %s )' % (ph, split_imp(ST_DVS)[1]))
    dvp = parse_conj(split_imp(ST_DVS)[1])
    rdn = w.s([dvs], 'simp1d', '( %s -> %s )' % (ph, dvp[0]))
    rdlt = w.s([dvs], 'simp2d', '( %s -> %s )' % (ph, dvp[1]))
    rdmi = w.s([dvs], 'simp3d', '( %s -> %s )' % (ph, dvp[2]))
    idi = w.s([], 'id', '( i = y -> i = y )')
    cgy, newy = w.wcongr('( ( 2 ^ i ) x. G ) <_ F', {'i': 'y'}, 'i = y', {'i': idi})
    cb_ = w.s([cgy], 'cbvralvw', '( %s <-> A. y e. ( 0 ..^ %s ) ( ( 2 ^ y ) x. G ) <_ F )' % (dvp[2], RD))
    rdmy = w.s([rdmi, cb_], 'sylib', '( %s -> A. y e. ( 0 ..^ %s ) ( ( 2 ^ y ) x. G ) <_ F )' % (ph, RD))
    dsl = split_imp(tsub_text(ST_DVSLE, {'N': NF}))
    rdle = w.s([w.s([fg, w.s([nfn, fl2n], 'jca', '( %s -> ( %s e. NN0 /\\ F < ( 2 ^ %s ) ) )' % (ph, NF, NF))], 'jca', '( %s -> %s )' % (ph, dsl[0])),
                w.inst('tmidvsle')], 'syl', '( %s -> %s )' % (ph, dsl[1]))
    ex = {'%s e. NN0' % RD: rdn, 'F < ( ( 2 ^ %s ) x. G )' % RD: rdlt, 'A. y e. ( 0 ..^ %s ) ( ( 2 ^ y ) x. G ) <_ F' % RD: rdmy, '%s <_ %s' % (RD, NF): rdle}
    st, cc = inst(w, ph, 'tmimodfr', {'R': RD}, Bld(w, ph, c, ex))
    assert cc == CONCL_MODF
    w.lines[-1] = 'qed:' + w.lines[-1].split(':', 1)[1]
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
