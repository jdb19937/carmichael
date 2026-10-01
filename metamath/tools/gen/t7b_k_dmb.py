"""T7b: the canonical division wrappers at the machine (Canon.lean
` divmodC_le_B ` , ` divC_le_B ` , ` modC_le_B ` ) on the installation
predicates: ~ tmidmr at ` R := ` the number of doublings ( ~ tmidvs ) and the
stack family ` P' := ` its mpt, then ` dropNum ` / ` canonNum ` , the bound by
~ tmddivb .

    MM_DB=sorties/t7b.mm python3 tools/gen/t7b_k_dmb.py tmidivmodcb tmidivcb tmimodcb
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t7blib import *
from cl import Closure
from lin import linarith, lineq, nlinarith
from t7_e_cmp import machine
from t7b_j_dmc import STMT_DMR, XR_, HR_, BDM, DATA_M
from t7b_f_nat import RD, ST_DVS, ST_DVSLE

SEL = sys.argv[1:]
K6 = ['K', 'J', 'I', "I'", 'I"', 'I0']
ENF, ENGG = '( encNatGam ` F )', '( encNatGam ` G )'
DATA_W = ((('F e. NN0', 'G e. NN', 'N e. NN0'), ('F < ( 2 ^ N )', 'G < ( 2 ^ N )')),
          ((WRD('X', GAM), WRD('Y', GAM), STKD('D')),
           ('( D ` K ) = %s' % CC(ENF, YXt('X')), '( D ` J ) = %s' % CC(ENGG, YXt('Y')))))
EMOD = '( ( encNatGam ` ( F mod G ) ) ++ ( <" 4 "> ++ X ) )'
EDIV = '( ( encNatGam ` ( |_ ` ( F / G ) ) ) ++ ( <" 4 "> ++ ( D ` I ) ) )'
TB = '( TMB ` N )'
CONF = {
    'tmidivmodcb': ('dmcc', UP(UP(UP('D', 'K', EMOD), 'I', EDIV), 'J', 'Y'),
                    "Lean ` divmodC_le_B ` : wherever ` divmodC x y q j s t ` is installed, with ` F ` on ` x ` and "
                    "` G ` ( ` 1 <_ G ` ) on ` y ` , both below ` 2 ^ N ` , ` x ` gets exactly ` F mod G ` , ` q ` gets "
                    "` |_ ( F / G ) ` pushed, ` y ` loses ` G ` and ` j ` , ` s ` , ` t ` are restored, within ` ( TMB ` N ) ` ."),
    'tmidivcb': ('divc', UP(UP(UP('D', 'K', 'X'), 'I', EDIV), 'J', 'Y'),
                 "Lean ` divC_le_B ` : wherever ` divC x y q j s t ` is installed, ` q ` gets ` |_ ( F / G ) ` pushed, "
                 "` F ` and ` G ` are consumed, within ` ( TMB ` N ) ` ."),
    'tmimodcb': ('modc', UP(UP('D', 'K', EMOD), 'J', 'Y'),
                 "Lean ` modC_le_B ` : wherever ` modC x y q j s t ` is installed, ` x ` gets exactly ` F mod G ` , "
                 "` G ` is consumed, ` q ` , ` j ` , ` s ` , ` t ` are restored, within ` ( TMB ` N ) ` ."),
}


RHYP = ('R e. NN0', 'R <_ %s' % NF, ('F < ( ( 2 ^ R ) x. G )', 'A. y e. ( 0 ..^ R ) ( ( 2 ^ y ) x. G ) <_ F'))
RLAB = {'tmidivmodcb': 'tmidmccr', 'tmidivcb': 'tmidivcr', 'tmimodcb': 'tmimodcr'}


def STMT(lab, rform=False):
    fn, post, _ = CONF[lab]
    f = FRAGS[fn]
    data = (DATA_W, RHYP) if rform else DATA_W
    tree = ((T_PHM7, f.pred()), (idx_tree(K6), dist_tree(K6)), data)
    return tree, TRI(CLN(f.entry(), SS, 'D'), CLN('E', SS, post), TB)


def final_wrapper(lab):
    T, C = STMT(lab)
    ph = cj(T)
    fname, post, desc = CONF[lab]
    w = W(lab, desc + '  The number of doublings is Lean\'s ` divSteps ` ( ~ tmidvs ).')
    c = Ctx(w, ph, T)
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
    st, cc = inst(w, ph, RLAB[lab], {'R': RD}, Bld(w, ph, c, ex))
    assert cc == C
    w.lines[-1] = 'qed:' + w.lines[-1].split(':', 1)[1]
    return w.run()


def wrapper(lab):
    fname, post, desc = CONF[lab]
    T, C = STMT(lab, rform=True)
    ph = cj(T)
    w = W(RLAB[lab], desc + '  Here ` R ` is any number of doublings with Lean\'s ` divSteps ` properties.')
    RD = 'R'
    c = Ctx(w, ph, T)
    mk = machine(w, ph, c, K6)
    phm, tv, seq = mk['phm'], mk['tv'], mk['seq']
    kk = mk['k']
    ne = ne_fn(w, ph, c, set(flat(dist_tree(K6))))
    dd = c[STKD('D')]
    f = FRAGS[fname]
    un = unfold_all(w, ph, c[f.pred()], fname, K6, 'P', 'E', rec=False)
    # the divmod call and its labels
    if fname == 'dmcc':
        Pdm, Edm = PL('P', 0), PL(PL('P', 1), 0)
    else:
        sub = 'divf' if fname == 'divc' else 'modf'
        un.update(unfold_all(w, ph, un[FRAGS[sub].pred(K6, 'T', 'M', PL('P', 0), PL(PL('P', 1), 0))], sub, K6, PL('P', 0),
                             PL(PL('P', 1), 0), rec=False))
        Pdm, Edm = PL(PL('P', 0), 0), PL(PL(PL('P', 0), 1), 0)
    base = {PHM: phm, 'T e. V': tv, MTY: mk['mt']}
    ex = dict(base); ex.update(un)
    for s_ in K6:
        ex['%s e. %s' % (s_, DG)] = kk[s_]['kd']
    for a_, b_ in [(a, b) for i_, a in enumerate(K6) for b in K6[i_ + 1:]]:
        ex['%s =/= %s' % (a_, b_)] = ne(a_, b_)
        ex['%s =/= %s' % (b_, a_)] = ne(b_, a_)
    fn_, gn, nn = c['F e. NN0'], c['G e. NN'], c['N e. NN0']
    flt, glt = c['F < ( 2 ^ N )'], c['G < ( 2 ^ N )']
    gn0 = w.s([gn, w.inst('nnnn0')], 'syl', '( %s -> G e. NN0 )' % ph)
    ef = w.s([fn_, w.inst('encnatcl')], 'syl', '( %s -> ( encodeNat ` F ) e. Word 2o )' % ph)
    eg = w.s([gn0, w.inst('encnatcl')], 'syl', '( %s -> %s e. Word 2o )' % (ph, EG))
    nfn = w.s([ef, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, NF))
    ngn = w.s([eg, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, NG))
    fl2n = w.s([w.s([ef, w.inst('tonatlt')], 'syl', '( %s -> ( toNat ` ( encodeNat ` F ) ) < ( 2 ^ %s ) )' % (ph, NF)),
                w.s([fn_, w.inst('tonatencnat')], 'syl', '( %s -> ( toNat ` ( encodeNat ` F ) ) = F )' % ph)], 'eqbrtrrd' if False else 'id', '') if False else None
    tln = w.s([ef, w.inst('tonatlt')], 'syl', '( %s -> ( toNat ` ( encodeNat ` F ) ) < ( 2 ^ %s ) )' % (ph, NF))
    tfe = w.s([fn_, w.inst('tonatencnat')], 'syl', '( %s -> ( toNat ` ( encodeNat ` F ) ) = F )' % ph)
    fl2n = w.s([tfe, tln], 'eqbrtrrd', '( %s -> F < ( 2 ^ %s ) )' % (ph, NF))
    rdn, rdlt, rdmy, rdle = c['R e. NN0'], c['F < ( ( 2 ^ R ) x. G )'], c['A. y e. ( 0 ..^ R ) ( ( 2 ^ y ) x. G ) <_ F'], c['R <_ %s' % NF]
    PDFR = tsub_text(PDF, {'R': RD})
    ex.update({'%s e. NN0' % RD: rdn, 'F < ( ( 2 ^ %s ) x. G )' % RD: rdlt, 'A. y e. ( 0 ..^ %s ) ( ( 2 ^ y ) x. G ) <_ F' % RD: rdmy,
               '%s <_ %s' % (RD, NF): rdle, '%s = %s' % (PDFR, PDFR): w.s([], 'eqidd', '( %s -> %s = %s )' % (ph, PDFR, PDFR))})
    mdm = {'P': Pdm, 'E': Edm, 'R': RD, "P'": PDFR}
    t1, c1 = inst(w, ph, 'tmidmr', mdm, Bld(w, ph, c, ex))
    Ca, Da, n1 = triple_parts(c1)
    XR, HR = XR_, tsub_text(HR_, {'R': RD})
    D2 = UP(UP(UP('D', 'K', XR), 'I', HR), 'J', 'Y')
    assert Da == CLN(Edm, SS, D2), Da
    cl = Closure(w, ph, {'F': ('NN0', fn_), 'G': ('NN', gn), 'N': ('NN0', nn), RD: ('NN0', rdn)})
    cl.leaf(NF, 'NN0', nfn); cl.leaf(NG, 'NN0', ngn)
    # the values: toNat of the remainder and quotient words
    fr = cl.mem('F', 'RR'); gp = w.s([gn], 'nnrpd', '( %s -> G e. RR+ )' % ph)
    md = '( F mod G )'; fq = '( |_ ` ( F / G ) )'
    mdn = w.s([cl.mem('F', 'ZZ'), gn, w.inst('zmodcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, md))
    fqn = w.s([fn_, gn, w.inst('fldivnn0')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, fq))
    cl.leaf(md, 'NN0', mdn); cl.leaf(fq, 'NN0', fqn)
    mv = w.s([fr, gp, w.inst('modvalr')], 'syl2anc', '( %s -> %s = ( F - ( %s x. G ) ) )' % (ph, md, fq))
    mle = nlinarith(w, ph, [mv, cl.ge0(fq), cl.ge0('G')], '%s <_ F' % md, closure=cl, atoms=[fq, md])
    cl.atom('( 2 ^ %s )' % NF)
    mlt = linarith(w, ph, [mle, fl2n], '%s < ( 2 ^ %s )' % (md, NF), closure=cl, atoms=[md])
    XB = '( %s bwrd %s )' % (md, NF)
    txb = w.s([mdn, nfn, mlt, w.inst('tonatbwrd2')], 'syl3anc', '( %s -> ( toNat ` %s ) = %s )' % (ph, XB, md))
    # floor ( F / G ) < 2 ^ RD
    PR = '( 2 ^ %s )' % RD
    prn = w.s([closed(w, ph, '2nn', '2 e. NN'), rdn, w.inst('nnexpcl')], 'syl2anc', '( %s -> %s e. NN )' % (ph, PR))
    cl.leaf(PR, 'NN', prn)
    fle = w.s([fr, gp, w.inst('fldivle')], 'syl2anc', '( %s -> %s <_ ( F / G ) )' % (ph, fq))
    ldm = w.s([fr, cl.mem(PR, 'RR'), w.s([cl.mem('G', 'RR'), cl.gt0('G')], 'jca', '( %s -> ( G e. RR /\\ 0 < G ) )' % ph), w.inst('ltdivmul')], 'syl3anc',
              '( %s -> ( ( F / G ) < %s <-> F < ( G x. %s ) ) )' % (ph, PR, PR))
    cm = w.s([cl.mem(PR, 'CC'), cl.mem('G', 'CC')], 'mulcomd', '( %s -> ( %s x. G ) = ( G x. %s ) )' % (ph, PR, PR))
    fgl = w.s([rdlt, cm], 'breqtrd', '( %s -> F < ( G x. %s ) )' % (ph, PR))
    fdl = w.s([fgl, ldm], 'mpbird', '( %s -> ( F / G ) < %s )' % (ph, PR))
    cl.atom('( F / G )'); cl.have('( F / G )', 'RR', cl.mem('( F / G )', 'RR'))
    fqlt = linarith(w, ph, [fle, fdl], '%s < %s' % (fq, PR), closure=cl, atoms=[fq, PR])
    QB = '( %s bwrd %s )' % (fq, RD)
    tqb = w.s([fqn, rdn, fqlt, w.inst('tonatbwrd2')], 'syl3anc', '( %s -> ( toNat ` %s ) = %s )' % (ph, QB, fq))
    xbw = w.s([cl.mem(md, 'ZZ'), nfn, w.inst('bwrdcl')], 'syl2anc', '( %s -> %s e. Word 2o )' % (ph, XB))
    qbw = w.s([cl.mem(fq, 'ZZ'), rdn, w.inst('bwrdcl')], 'syl2anc', '( %s -> %s e. Word 2o )' % (ph, QB))
    togk = lambda X, s_, g: w.s([g, kk[s_]['wge']], 'eleqtrrd', '( %s -> %s e. Word %s )' % (ph, X, GX(s_)))
    dIg = w.s([stkfv(w, ph, 'D', 'I', tv, dd, kk['I']['kd']), kk['I']['wge']], 'eleqtrd', "( %s -> ( D ` I ) e. Word Gamma' )" % ph)
    xrg = wgcat(w, ph, '( inclBool o. %s )' % XB, YXt('X'), wib(w, ph, XB, xbw), wg4(w, ph, 'X', c[WRD('X', GAM)]))
    hrg = wgcat(w, ph, '( inclBool o. %s )' % QB, YXt('( D ` I )'), wib(w, ph, QB, qbw), wg4(w, ph, '( D ` I )', dIg))
    S2 = Stacks(w, ph, mk, 'D', dd, ne, {}).upd('K', XR, xrg).upd('I', HR, hrg).upd('J', 'Y', c[WRD('Y', GAM)])
    assert S2.D == D2
    # the canonical words
    def canon(Dc, Sc, s_, L_, Xrest, P_, E_, lw):
        m = {'K': s_, 'J': 'I"', 'P': P_, 'E': E_, 'L': L_, 'X': Xrest, 'D': Dc}
        exx = dict(ex)
        exx.update({WRD(L_, '2o'): lw, WRD(Xrest, GAM): (c[WRD('X', GAM)] if Xrest == 'X' else dIg), STKD(Dc): Sc.memb,
                    '( %s ` %s ) = %s' % (Dc, s_, CC('( inclBool o. %s )' % L_, YXt(Xrest))): Sc.val(s_)[1]})
        return inst(w, ph, 'tmicans', m, Bld(w, ph, c, exx))
    steps = [(t1, Ca, Da, n1)]
    cur_S = S2
    if fname == 'dmcc':
        t2, c2 = canon(D2, S2, 'K', XB, 'X', PL('P', 1), PL(PL('P', 2), 0), xbw)
        C2, D2b, n2 = triple_parts(c2)
        A_ = CC('( encNatGam ` ( toNat ` %s ) )' % XB, YXt('X'))
        S3 = S2.upd('K', A_, wgcat(w, ph, '( encNatGam ` ( toNat ` %s ) )' % XB, YXt('X'),
                                   w.s([w.s([xbw, w.inst('tonatcl')], 'syl', '( %s -> ( toNat ` %s ) e. NN0 )' % (ph, XB)), w.inst('encnatgamcl')], 'syl',
                                       "( %s -> ( encNatGam ` ( toNat ` %s ) ) e. Word Gamma' )" % (ph, XB)), wg4(w, ph, 'X', c[WRD('X', GAM)])))
        assert D2b == CLN(PL(PL('P', 2), 0), SS, S3.D)
        steps.append((t2, C2, D2b, n2))
        t3, c3 = canon(S3.D, S3, 'I', QB, '( D ` I )', PL('P', 2), 'E', qbw)
        C3, D3b, n3 = triple_parts(c3)
        B_ = CC('( encNatGam ` ( toNat ` %s ) )' % QB, YXt('( D ` I )'))
        steps.append((t3, C3, D3b, n3))
        FIN0 = UP(S3.D, 'I', B_)
    elif fname == 'divc':
        Wd = '( inclBool o. %s )' % XB
        wdb = w.s([xbw, w.inst('tmcibw')], 'syl', '( %s -> %s e. Word %s )' % (ph, Wd, BITS))
        # the drop wants UPD( D' , K , ( W ++ ( <" 4 "> ++ X ) ) ): D2 = UPD( UPD( UPD( D , K , XR ) , I , HR ) , J , Y )
        # rewrite D2 = UPD( UPD( UPD( D , I , HR ) , J , Y ) , K , XR )
        SA = Stacks(w, ph, mk, 'D', dd, ne, {}).upd('I', HR, hrg)
        SB = SA.upd('J', 'Y', c[WRD('Y', GAM)])
        e1 = upc(w, ph, 'D', 'K', XR, 'I', HR, tv, dd, ne('K', 'I'), kk['K']['kd'], togk(XR, 'K', xrg), kk['I']['kd'], togk(HR, 'I', hrg))
        r1, n1_ = w.rewrite(D2, {UP(UP('D', 'K', XR), 'I', HR): (UP(UP('D', 'I', HR), 'K', XR), e1)}, ph)
        e2 = upc(w, ph, SA.D, 'K', XR, 'J', 'Y', tv, SA.memb, ne('K', 'J'), kk['K']['kd'], togk(XR, 'K', xrg), kk['J']['kd'], togk('Y', 'J', c[WRD('Y', GAM)]))
        DP = UP(SB.D, 'K', XR)
        deq = w.s([r1, e2], 'eqtrd', '( %s -> %s = %s )' % (ph, D2, DP))
        t1b, Ca, Da2, n1 = hrrw(w, ph, t1, Ca, Da, n1, deq=clneq(w, ph, Edm, SS, deq, D2, DP))
        steps = [(t1b, Ca, Da2, n1)]
        m = {'K': 'K', 'P': PL(PL('P', 0), 1), 'E': PL(PL('P', 1), 0), 'W': Wd, 'X': 'X', 'D': SB.D}
        exx = dict(ex); exx.update({WRD(Wd, BITS): wdb, STKD(SB.D): SB.memb})
        t2, c2 = inst(w, ph, 'tmidrop', m, Bld(w, ph, c, exx))
        C2, D2b, n2 = triple_parts(c2)
        steps.append((t2, C2, D2b, n2))
        S3 = SB.upd('K', 'X', c[WRD('X', GAM)])
        t3, c3 = canon(S3.D, S3, 'I', QB, '( D ` I )', PL('P', 1), 'E', qbw)
        C3, D3b, n3 = triple_parts(c3)
        B_ = CC('( encNatGam ` ( toNat ` %s ) )' % QB, YXt('( D ` I )'))
        steps.append((t3, C3, D3b, n3))
        FIN0 = UP(S3.D, 'I', B_)
    else:
        Wq = '( inclBool o. %s )' % QB
        wqb = w.s([qbw, w.inst('tmcibw')], 'syl', '( %s -> %s e. Word %s )' % (ph, Wq, BITS))
        # D2 = UPD( UPD( UPD( D , K , XR ) , J , Y ) , I , HR )
        SA = Stacks(w, ph, mk, 'D', dd, ne, {}).upd('K', XR, xrg)
        SB = SA.upd('J', 'Y', c[WRD('Y', GAM)])
        e2 = upc(w, ph, SA.D, 'I', HR, 'J', 'Y', tv, SA.memb, ne('I', 'J'), kk['I']['kd'], togk(HR, 'I', hrg), kk['J']['kd'], togk('Y', 'J', c[WRD('Y', GAM)]))
        DP = UP(SB.D, 'I', HR)
        t1b, Ca, Da2, n1 = hrrw(w, ph, t1, Ca, Da, n1, deq=clneq(w, ph, Edm, SS, e2, D2, DP))
        steps = [(t1b, Ca, Da2, n1)]
        m = {'K': 'I', 'P': PL(PL('P', 0), 1), 'E': PL(PL('P', 1), 0), 'W': Wq, 'X': '( D ` I )', 'D': SB.D}
        exx = dict(ex); exx.update({WRD(Wq, BITS): wqb, STKD(SB.D): SB.memb, WRD('( D ` I )', GAM): dIg})
        t2, c2 = inst(w, ph, 'tmidrop', m, Bld(w, ph, c, exx))
        C2, D2b, n2 = triple_parts(c2)
        steps.append((t2, C2, D2b, n2))
        S3 = SB.upd('I', '( D ` I )', dIg)
        t3, c3 = canon(S3.D, S3, 'K', XB, 'X', PL('P', 1), 'E', xbw)
        C3, D3b, n3 = triple_parts(c3)
        A_ = CC('( encNatGam ` ( toNat ` %s ) )' % XB, YXt('X'))
        steps.append((t3, C3, D3b, n3))
        FIN0 = UP(S3.D, 'K', A_)
    # ---- sequence
    t, C_, D_, n_ = steps[0]
    for (tb, Cb, Db, nb) in steps[1:]:
        assert Cb == D_, (Cb, D_)
        t = hrseq(w, ph, phm, t, tb, C_, D_, Db, n_, nb)
        n_ = '( %s + %s )' % (n_, nb)
        D_ = Db
    assert D_ == CLN('E', SS, FIN0), (D_, FIN0)
    # ---- the final stacks
    fin_eq = final_stacks(w, ph, mk, dd, ne, fname, FIN0, post, XB, QB, txb, tqb, xrg, hrg, dIg, c)
    t, C_, D_, n_ = hrrw(w, ph, t, C_, D_, n_, deq=clneq(w, ph, 'E', SS, fin_eq, FIN0, post))
    # ---- the bound: n_ <_ LHS of tmddivb <_ ( TMB ` N )
    le_bound(w, ph, c, cl, t, C_, D_, n_, phm, fname, XB, QB, xbw, qbw, rdle, nfn, ngn, fn_, gn0, nn, flt, glt)
    return w.run()


def final_stacks(w, ph, mk, dd, ne, fname, FIN0, post, XB, QB, txb, tqb, xrg, hrg, dIg, c):
    """( ph -> FIN0 = post )"""
    XR, HR = XR_, HR_
    AX = CC('( encNatGam ` ( toNat ` %s ) )' % XB, YXt('X'))
    BQ = CC('( encNatGam ` ( toNat ` %s ) )' % QB, YXt('( D ` I )'))
    ax = w.s([w.s([txb], 'fveq2d', '( %s -> ( encNatGam ` ( toNat ` %s ) ) = ( encNatGam ` ( F mod G ) ) )' % (ph, XB))], 'oveq1d', '( %s -> %s = %s )' % (ph, AX, EMOD))
    bq = w.s([w.s([tqb], 'fveq2d', '( %s -> ( encNatGam ` ( toNat ` %s ) ) = ( encNatGam ` ( |_ ` ( F / G ) ) ) )' % (ph, QB))], 'oveq1d', '( %s -> %s = %s )' % (ph, BQ, EDIV))
    def encg(L_, Xr, g):
        tn = w.s([w.s([w.s([L_ and c[WRD('X', GAM)]], 'id', '') if False else None], '', '') if False else None], '', '') if False else None
        return None
    xbw_ = None
    def gw(L_, Xr, xg):
        lw = w.s([w.s([], 'id', '') if False else None], '', '') if False else None
        return None
    gam = {XR: xrg, HR: hrg, 'Y': c[WRD('Y', GAM)], 'X': c[WRD('X', GAM)], '( D ` I )': dIg}
    for L_, V_, Xr in [(XB, AX, 'X'), (QB, BQ, '( D ` I )')]:
        lw = w.s([w.s([w.s([], 'id', '') if False else None], '', '') if False else None], '', '') if False else None
        ww = gam['X'] if Xr == 'X' else dIg
        tnn = w.s([w.s([w.s([], 'id', '') if False else None], '', '') if False else None], '', '') if False else None
        gam[V_] = None
    # typings of the canonical words: from the toNat values
    for L_, V_, Xr, tv_eq, val in [(XB, AX, 'X', txb, '( F mod G )'), (QB, BQ, '( D ` I )', tqb, '( |_ ` ( F / G ) )')]:
        vn = w.s([w.s([w.s([], 'id', '') if False else None], '', '') if False else None], '', '') if False else None
        cl_ = Closure(w, ph, {'F': ('NN0', c['F e. NN0']), 'G': ('NN', c['G e. NN'])})
        valn = cl_.mem(val, 'NN0')
        tn = w.s([tv_eq, valn], 'eqeltrrd' if False else 'eqeltrd', '( %s -> ( toNat ` %s ) e. NN0 )' % (ph, L_))
        eg_ = w.s([tn, w.inst('encnatgamcl')], 'syl', "( %s -> ( encNatGam ` ( toNat ` %s ) ) e. Word Gamma' )" % (ph, L_))
        gam[V_] = wgcat(w, ph, '( encNatGam ` ( toNat ` %s ) )' % L_, YXt(Xr), eg_, wg4(w, ph, Xr, gam[Xr]))
    if fname == 'dmcc':
        chain = [('K', XR), ('I', HR), ('J', 'Y'), ('K', AX), ('I', BQ)]
        order = ['K', 'I', 'J']
    elif fname == 'divc':
        chain = [('I', HR), ('J', 'Y'), ('K', 'X'), ('I', BQ)]
        order = ['K', 'I', 'J']
    else:
        chain = [('K', XR), ('J', 'Y'), ('I', '( D ` I )'), ('K', AX)]
        order = ['K', 'J']
    assert chain_text('D', chain) == FIN0, (chain_text('D', chain), FIN0)
    st, out = stk_normalize(w, ph, mk, 'D', dd, ne, chain, gam, order)
    nt = chain_text('D', out)
    r, n = w.rewrite(nt, {AX: (EMOD, ax), BQ: (EDIV, bq)} if fname == 'dmcc' else ({BQ: (EDIV, bq)} if fname == 'divc' else {AX: (EMOD, ax)}), ph)
    assert n == post, (n, post)
    return w.s([st, r], 'eqtrd', '( %s -> %s = %s )' % (ph, FIN0, post))


def le_bound(w, ph, c, cl, t, C_, D_, n_, phm, fname, XB, QB, xbw, qbw, rdle, nfn, ngn, fn_, gn0, nn, flt, glt):
    LXB, LQB = '( # ` %s )' % XB, '( # ` %s )' % QB
    xl = w.s([cl.mem('( F mod G )', 'ZZ'), nfn, w.inst('bwrdlen')], 'syl2anc', '( %s -> %s = %s )' % (ph, LXB, NF))
    ql = w.s([cl.mem('( |_ ` ( F / G ) )', 'ZZ'), c_rd(cl), w.inst('bwrdlen')], 'syl2anc', '( %s -> %s = %s )' % (ph, LQB, 'R'))
    cl.leaf(LXB, 'NN0', w.s([xbw, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, LXB)))
    cl.leaf(LQB, 'NN0', w.s([qbw, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, LQB)))
    for extra_len in ['( # ` ( inclBool o. %s ) )' % XB, '( # ` ( inclBool o. %s ) )' % QB]:
        pass
    hyps = [xl, ql, rdle, cl.ge0(NF), cl.ge0(NG)]
    if fname in ('divc', 'modc'):
        L_ = XB if fname == 'divc' else QB
        lw_ = xbw if fname == 'divc' else qbw
        ib = '( # ` ( inclBool o. %s ) )' % L_
        bl_ = w.s([lw_, w.inst('bwmaplen')], 'syl', '( %s -> %s = ( # ` %s ) )' % (ph, ib, L_))
        cl.leaf(ib, 'NN0', w.s([w.s([lw_, w.inst('tmcibw')], 'syl', '( %s -> ( inclBool o. %s ) e. Word %s )' % (ph, L_, BITS)), w.inst('lencl')], 'syl',
                              '( %s -> %s e. NN0 )' % (ph, ib)))
        hyps.append(bl_)
    LHS = '( ( %s x. ( ( ; 2 3 x. ( %s + %s ) ) + ; 6 0 ) ) + ( ( ; 1 4 x. ( %s + %s ) ) + ; 3 7 ) )' % (NF, NF, NG, NF, NG)
    le1 = nlinarith(w, ph, hyps, '%s <_ %s' % (n_, LHS), closure=cl, atoms=[NF, NG, LXB, LQB, 'R'])
    # tmddivb at A := n , D := g , C := 14 , M := N
    fe = w.s([fn_, nn, flt, w.inst('encnatlenpow')], 'syl3anc', '( %s -> %s <_ N )' % (ph, NF))
    ge = w.s([gn0, nn, glt, w.inst('encnatlenpow')], 'syl3anc', '( %s -> %s <_ N )' % (ph, NG))
    c14 = w.s([], 'nn0' if False else '1nn0', '1 e. NN0') if False else None
    n14 = cl.mem('; 1 4', 'NN0')
    l14 = w.s([w.s([], 'leidi' if False else 'id', '') if False else None], '', '') if False else None
    l14 = w.s([w.s([cl.mem('; 1 4', 'RR')], 'leidd', '( %s -> ; 1 4 <_ ; 1 4 )' % ph)], 'id', '') if False else w.s([cl.mem('; 1 4', 'RR')], 'leidd', '( %s -> ; 1 4 <_ ; 1 4 )' % ph)
    ante = '( ( %s e. NN0 /\\ %s e. NN0 /\\ N e. NN0 ) /\\ ( ; 1 4 e. NN0 /\\ ; 1 4 <_ ; 1 4 ) /\\ ( %s <_ N /\\ %s <_ N ) )' % (NF, NG, NF, NG)
    j = w.s([w.s([nfn, ngn, nn], '3jca', '( %s -> ( %s e. NN0 /\\ %s e. NN0 /\\ N e. NN0 ) )' % (ph, NF, NG)),
             w.s([n14, l14], 'jca', '( %s -> ( ; 1 4 e. NN0 /\\ ; 1 4 <_ ; 1 4 ) )' % ph),
             w.s([fe, ge], 'jca', '( %s -> ( %s <_ N /\\ %s <_ N ) )' % (ph, NF, NG))], '3jca', '( %s -> %s )' % (ph, ante))
    db = w.s([j, w.inst('tmddivb')], 'syl', '( %s -> %s <_ ( TMB ` N ) )' % (ph, LHS))
    tb = w.s([w.s([nn, w.inst('tmbcl')], 'syl', '( %s -> ( TMB ` N ) e. NN )' % ph), w.inst('nnnn0')], 'syl', '( %s -> ( TMB ` N ) e. NN0 )' % ph)
    cl.leaf('( TMB ` N )', 'NN0', tb)
    le2 = w.s([cl.mem(n_, 'RR'), cl.mem(LHS, 'RR'), cl.mem('( TMB ` N )', 'RR'), le1, db], 'letrd', '( %s -> %s <_ ( TMB ` N ) )' % (ph, n_))
    hrle(w, ph, phm, t, C_, D_, n_, TB, tb, le2, qed=True)


def c_rd(cl):
    return cl.mem('R', 'NN0')


if __name__ == '__main__':
    for l in SEL:
        if l in RLAB.values():
            wrapper([k for k, v in RLAB.items() if v == l][0])
        else:
            final_wrapper(l)
