"""T15 (k): the assembly: prefix bound, step function, time function, carmtmw."""
import os, sys, json, re
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from t15lib import *
import num
import lin
lin.FASTPATH = True
from lin import linarith

E2 = '( ell2 ` N )'
E3 = '( ell3 ` N )'
MM = '( %s x. %s )' % (E2, E3)
Z = '( # ` ( encodeNat ` N ) )'
BPRE = '( ( 7 x. %s ) + ; 7 0 )' % Z


def t15zb():
    w = W('t15zb', 'The prefix of route beta costs at most exp ( 2 ell2 n ell3 n ) once ell3 n >= 1.')
    ph = '( N e. ( ZZ>= ` ; 1 6 ) /\\ ( 1 <_ %s /\\ 1 <_ %s /\\ ; ; ; 2 4 0 0 <_ %s ) )' % (E2, E3, MM)
    S = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (ph, f))
    nu = S([], 'simpl', 'N e. ( ZZ>= ` ; 1 6 )')
    h = S([], 'simpr', '( 1 <_ %s /\\ 1 <_ %s /\\ ; ; ; 2 4 0 0 <_ %s )' % (E2, E3, MM))
    l2 = S([h], 'simp1d', '1 <_ %s' % E2); l3 = S([h], 'simp2d', '1 <_ %s' % E3); lm = S([h], 'simp3d', '; ; ; 2 4 0 0 <_ %s' % MM)
    n0 = S([S([w.s([num.nn0(w, 16)], 'a1i', '( %s -> ; 1 6 e. NN0 )' % ph), nu, w.inst('eluznn0')], 'syl2anc', 'N e. NN0')], 'id', '') if False else None
    n0 = S([w.s([num.nn0(w, 16)], 'a1i', '( %s -> ; 1 6 e. NN0 )' % ph), nu, w.inst('eluznn0')], 'syl2anc', 'N e. NN0')
    nr = S([n0], 'nn0red', 'N e. RR')
    le16 = S([nu, w.inst('eluzle')], 'syl', '; 1 6 <_ N')
    one = S([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR')
    r16 = S([num.re_nat(w, 16)], 'a1i', '; 1 6 e. RR')
    lt1 = linarith(w, ph, [le16], '1 < N', leaves={'N': nr})
    npos = linarith(w, ph, [le16], '0 < N', leaves={'N': nr})
    nrp = S([nr, npos], 'elrpd', 'N e. RR+')
    lb = S([nrp, w.inst('loggt0b')], 'syl', '( 0 < ( log ` N ) <-> 1 < N )')
    lp = S([lt1, lb], 'mpbird', '0 < ( log ` N )')
    lr = S([nrp, w.inst('relogcl')], 'syl', '( log ` N ) e. RR')
    lrp = S([lr, lp], 'elrpd', '( log ` N ) e. RR+')
    e2v = S([n0, w.inst('ell2val')], 'syl', '%s = ( log ` ( log ` N ) )' % E2)
    rf = S([lrp, w.inst('reeflog')], 'syl', '( exp ` ( log ` ( log ` N ) ) ) = ( log ` N )')
    ef2 = S([S([e2v], 'fveq2d', '( exp ` %s ) = ( exp ` ( log ` ( log ` N ) ) )' % E2), rf], 'eqtrd', '( exp ` %s ) = ( log ` N )' % E2)
    e2r = S([S([lrp, w.inst('relogcl')], 'syl', '( log ` ( log ` N ) ) e. RR'), e2v], 'eqeltrrd', '%s e. RR' % E2) if False else None
    e2r = S([e2v, S([lrp, w.inst('relogcl')], 'syl', '( log ` ( log ` N ) ) e. RR')], 'eqeltrd', '%s e. RR' % E2)
    # ell3 real: 1 <_ ell3 with ell3 = log ( ell2 ) , ell2 > 0
    e2p = linarith(w, ph, [l2], '0 < %s' % E2, leaves={E2: e2r})
    e2rp = S([e2r, e2p], 'elrpd', '%s e. RR+' % E2)
    e3v = S([n0, w.inst('ell3val')], 'syl', '%s = ( log ` %s )' % (E3, E2))
    e3r = S([e3v, S([e2rp, w.inst('relogcl')], 'syl', '( log ` %s ) e. RR' % E2)], 'eqeltrd', '%s e. RR' % E3)
    mr = S([e2r, e3r], 'remulcld', '%s e. RR' % MM)
    # ell2 <_ M
    e3m1 = S([e3r, one], 'resubcld', '( %s - 1 ) e. RR' % E3)
    e20 = linarith(w, ph, [l2], '0 <_ %s' % E2, leaves={E2: e2r})
    e3m0 = linarith(w, ph, [l3], '0 <_ ( %s - 1 )' % E3, leaves={E3: e3r})
    pm = S([e2r, e3m1, e20, e3m0], 'mulge0d', '0 <_ ( %s x. ( %s - 1 ) )' % (E2, E3))
    e2c = S([e2r], 'recnd', '%s e. CC' % E2); e3c = S([e3r], 'recnd', '%s e. CC' % E3)
    onec = S([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '1 e. CC')
    sd = S([e2c, e3c, onec], 'subdid', '( %s x. ( %s - 1 ) ) = ( %s - ( %s x. 1 ) )' % (E2, E3, MM, E2))
    mr1 = S([e2c], 'mulridd', '( %s x. 1 ) = %s' % (E2, E2))
    sd2 = S([sd, S([mr1], 'oveq2d', '( %s - ( %s x. 1 ) ) = ( %s - %s )' % (MM, E2, MM, E2))], 'eqtrd', '( %s x. ( %s - 1 ) ) = ( %s - %s )' % (E2, E3, MM, E2))
    pmr = S([e2r, e3m1], 'remulcld', '( %s x. ( %s - 1 ) ) e. RR' % (E2, E3))
    le2m = linarith(w, ph, [pm, sd2], '%s <_ %s' % (E2, MM), leaves={E2: e2r, MM: mr, '( %s x. ( %s - 1 ) )' % (E2, E3): pmr})
    efl = S([S([e2r, mr, w.inst('efle')], 'syl2anc', '( %s <_ %s <-> ( exp ` %s ) <_ ( exp ` %s ) )' % (E2, MM, E2, MM)), le2m], 'mpbid' if False else 'mpbird', '') if False else None
    efb = S([e2r, mr, w.inst('efle')], 'syl2anc', '( %s <_ %s <-> ( exp ` %s ) <_ ( exp ` %s ) )' % (E2, MM, E2, MM))
    efl = S([le2m, efb], 'mpbid', '( exp ` %s ) <_ ( exp ` %s )' % (E2, MM))
    E = '( exp ` %s )' % MM
    lnE = S([ef2, efl], 'eqbrtrrd', '( log ` N ) <_ %s' % E)
    # Z bound
    nn = S([nu, w.inst('eluzelz')], 'syl', 'N e. ZZ') if False else None
    nnn = S([n0, S([npos], 'id', '') if False else npos], 'elnnnn0d' if False else 'elnnnn0b', '') if False else None
    nN = S([n0, npos], 'nn0gt0d' if False else 'jca', '( N e. NN0 /\\ 0 < N )')
    nNN = S([nN, w.s([], 'elnnnn0b', '( N e. NN <-> ( N e. NN0 /\\ 0 < N ) )')], 'sylibr', 'N e. NN')
    zl = S([n0, w.inst('encnatlennlog')], 'syl', '%s <_ ( ( 2 Nlog N ) + 1 )' % Z)
    nl = S([nNN, w.inst('nlog2log')], 'syl', '( 2 Nlog N ) <_ ( 2 x. ( log ` N ) )')
    zr = S([S([S([n0, w.inst('encnatcl')], 'syl', '( encodeNat ` N ) e. Word 2o'), w.inst('lencl')], 'syl', '%s e. NN0' % Z)], 'nn0red', '%s e. RR' % Z)
    nlr = S([S([nNN, w.inst('nlogcl' if False else 'nlogcl')], 'syl', '( 2 Nlog N ) e. NN0') if False else None], 'id', '') if False else None
    # 2 Nlog N is real: from the bound itself use lin leaves: prove it in NN0
    nlr = S([S([S([w.s([], '2nn', '2 e. NN')], 'a1i', '2 e. NN') if False else S([w.s([], '2z', '2 e. ZZ')], 'a1i', '2 e. ZZ'), nNN], 'jca', '( 2 e. ZZ /\\ N e. NN )') if False else nNN], 'id', '') if False else None
    mr0 = linarith(w, ph, [lm], '0 <_ %s' % MM, leaves={MM: mr})
    eb = S([mr, mr0, w.inst('bvefge1p')], 'syl2anc', '( 1 + %s ) <_ %s' % (MM, E))
    er = S([mr], 'reefcld', '%s e. RR' % E)
    ge = linarith(w, ph, [eb, lm], '; ; ; 2 4 0 1 <_ %s' % E, leaves={MM: mr, E: er})
    e0 = linarith(w, ph, [ge], '0 <_ %s' % E, leaves={E: er})
    r24 = S([num.re_nat(w, 2401)], 'a1i', '; ; ; 2 4 0 1 e. RR')
    x1 = S([r24, er, S([er, e0], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (E, E))], '3jca', '( ; ; ; 2 4 0 1 e. RR /\\ %s e. RR /\\ ( %s e. RR /\\ 0 <_ %s ) )' % (E, E, E))
    pr = S([x1, ge, w.inst('lemul1a')], 'syl2anc', '( ; ; ; 2 4 0 1 x. %s ) <_ ( %s x. %s )' % (E, E, E))
    EE = '( %s x. %s )' % (E, E)
    eer = S([er, er], 'remulcld', '%s e. RR' % EE)
    return w, ph, S, dict(zl=zl, nl=nl, lnE=lnE, ge=ge, pr=pr, zr=zr, lr=lr, er=er, eer=eer, mr=mr, nNN=nNN, E=E, EE=EE)


def t15zb_full():
    w, ph, S, d = t15zb()
    E, EE = d['E'], d['EE']
    NL = '( 2 Nlog N )'
    # ( 2 Nlog N ) real
    nln = S([d['nNN'], w.inst('nlogclnn' if False else 'nnnn0')], 'syl', 'N e. NN0') if False else None
    nlr = S([d['zl']], 'id', '') if False else None
    fac = linarith(w, ph, [d['zl'], d['nl'], d['lnE'], d['ge'], d['pr']], '%s <_ %s' % (BPRE, EE),
                   leaves={Z: d['zr'], NL: nlrstep(w, S, d), '( log ` N )': d['lr'], E: d['er'], EE: d['eer']})
    mc = S([d['mr']], 'recnd', '%s e. CC' % MM)
    ea = S([mc, mc, w.inst('efadd')], 'syl2anc', '( exp ` ( %s + %s ) ) = %s' % (MM, MM, EE))
    t2 = S([mc, w.inst('2times')], 'syl', '( 2 x. %s ) = ( %s + %s )' % (MM, MM, MM))
    e2 = S([S([t2], 'fveq2d', '( exp ` ( 2 x. %s ) ) = ( exp ` ( %s + %s ) )' % (MM, MM, MM)), ea], 'eqtrd', '( exp ` ( 2 x. %s ) ) = %s' % (MM, EE))
    w.qed([fac, e2], 'breqtrrd', '( %s -> %s <_ ( exp ` ( 2 x. %s ) ) )' % (ph, BPRE, MM))
    return w


def nlrstep(w, S, d):
    """( ph -> ( 2 Nlog N ) e. RR )"""
    # ( 2 Nlog N ) <_ 2 log N and it is an integer: use nlogcl if present
    two = S([w.s([], '2nn0', '2 e. NN0')], 'a1i', '2 e. NN0')
    nn0 = S([d['nNN']], 'nnnn0d', 'N e. NN0')
    return S([S([two, nn0, w.inst('nlogcl')], 'syl2anc', '( 2 Nlog N ) e. NN0')], 'nn0red', '( 2 Nlog N ) e. RR')


GENS = {'t15zb': t15zb_full}



def _sb():
    import t15_g_pre as GP
    A_, B_ = split_imp(stmt_of('t15runb'))
    C_, P_, N_ = GP.parse_tri(B_.replace('( ( TMTy C K ) TM2Hoare ( TMProg C K ) )', '( T TM2Hoare M )'))
    pre = '( ( %s + ' % BPRE
    assert N_.startswith(pre) and N_.endswith(' ) + 1 )')
    return N_[len(pre):-len(' ) + 1 )')]


SB = _sb()
SCN = '( ( C ScTM K ) ` N )'
GETD = 'if ( ( 1st ` ( %s Search N ) ) = ( inr ` (/) ) , <. 0 , (/) >. , ( 2nd ` ( 1st ` ( %s Search N ) ) ) )' % (SCN, SCN)
ENC = '( ( 1st ` %s ) encodeOutput ( 2nd ` %s ) )' % (GETD, GETD)


def tx(t, v='x'):
    return subst_text(t, {'N': v})


GBODY = 'if ( x < ; 1 6 , ( %s + 1 ) , ( ( %s + %s ) + 1 ) )' % (tx(BPRE), tx(BPRE), tx(SB))
FBODY = 'if ( x < ; 1 6 , <. 0 , (/) >. , %s )' % tx(GETD)
GM = '( x e. NN0 |-> %s )' % GBODY
FM = '( x e. NN0 |-> %s )' % FBODY
MACH = '( TMMach C K )'


def t15out():
    w = W('t15out', 'The concrete machine outputs the encoding of f n within any bound above g n (f, g the output and step functions).')
    ph = '( ( ( C e. NN0 /\\ 1 <_ C ) /\\ K e. NN ) /\\ ( N e. NN0 /\\ Q e. NN0 /\\ ( %s ` N ) <_ Q ) )' % GM
    S = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (ph, f))
    c1 = S([], 'simpll', '( C e. NN0 /\\ 1 <_ C )')
    cn = S([c1], 'simpld', 'C e. NN0')
    kn = S([], 'simplr', 'K e. NN')
    tr = S([], 'simpr', '( N e. NN0 /\\ Q e. NN0 /\\ ( %s ` N ) <_ Q )' % GM)
    nn = S([tr], 'simp1d', 'N e. NN0'); qn = S([tr], 'simp2d', 'Q e. NN0'); gq = S([tr], 'simp3d', '( %s ` N ) <_ Q' % GM)
    ck = S([cn, kn], 'jca', '( C e. NN0 /\\ K e. NN )')
    GV = subst_text(GBODY, {'x': 'N'})
    FV = subst_text(FBODY, {'x': 'N'})
    gv, _ = fvm(w, ph, GM, None, 'x', 'NN0', GBODY, 'N', nn, S([], 'ifexd' if False else 'fvexd', '') if False else S([w.s([], 'ifex', '%s e. _V' % GV)], 'a1i', '%s e. _V' % GV))
    fv, _ = fvm(w, ph, FM, None, 'x', 'NN0', FBODY, 'N', nn, S([w.s([], 'ifex', '%s e. _V' % FV)], 'a1i', '%s e. _V' % FV))
    OUT = '( encNatGam ` N ) ( %s TM2OutputsInTime Q ) ( inl ` ( encodeOutput ` ( %s ` N ) ) )' % (MACH, FM)
    # small inputs
    ps = '( %s /\\ N < ; 1 6 )' % ph
    P = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (ps, f))
    sub = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (ps, f))
    lt = P([], 'simpr', 'N < ; 1 6')
    RS = '( %s + 1 )' % BPRE
    gs = P([sub(gv, '( %s ` N ) = %s' % (GM, GV)), P([lt], 'iftrued', '%s = %s' % (GV, RS))], 'eqtrd', '( %s ` N ) = %s' % (GM, RS))
    rq = P([gs, sub(gq, '( %s ` N ) <_ Q' % GM)], 'eqbrtrrd', '%s <_ Q' % RS)
    rs, frs = use(w, ps, 't15runs', {}, {'( C e. NN0 /\\ K e. NN )': sub(ck, '( C e. NN0 /\\ K e. NN )'), 'N e. NN0': sub(nn, 'N e. NN0'), 'N < ; 1 6': lt})
    g4 = P([w.s([w.s([], 'gamma4', "4 e. Gamma'"), w.inst('s1cl')], 'ax-mp', "<\" 4 \"> e. Word Gamma'")], 'a1i', "<\" 4 \"> e. Word Gamma'")
    Ls = {'( C e. NN0 /\\ K e. NN )': sub(ck, '( C e. NN0 /\\ K e. NN )'), 'N e. NN0': sub(nn, 'N e. NN0'), 'Q e. NN0': sub(qn, 'Q e. NN0'),
          "<\" 4 \"> e. Word Gamma'": g4, '%s <_ Q' % RS: rq, frs: rs}
    cs, fcs = use(w, ps, 't15conv', {'O': '<" 4 ">', 'R': RS}, Ls)
    fs = P([sub(fv, '( %s ` N ) = %s' % (FM, FV)), P([lt], 'iftrued', '%s = <. 0 , (/) >.' % FV)], 'eqtrd', '( %s ` N ) = <. 0 , (/) >.' % FM)
    e1 = P([fs], 'fveq2d', '( encodeOutput ` ( %s ` N ) ) = ( encodeOutput ` <. 0 , (/) >. )' % FM)
    e2 = w.s([], 'encoutfv', '( encodeOutput ` <. 0 , (/) >. ) = ( 0 encodeOutput (/) )')
    e3 = w.s([w.s([], '0nn0', '0 e. NN0'), w.inst('encoutnil')], 'ax-mp', '( 0 encodeOutput (/) ) = ( ( encNatGam ` 0 ) ++ <" 4 "> )')
    g0 = w.s([w.s([], '0nn0', '0 e. NN0'), w.inst('encnatgamval')], 'ax-mp', '( encNatGam ` 0 ) = ( inclBool o. ( encodeNat ` 0 ) )')
    g1 = w.s([w.s([], 'encnat0', '( encodeNat ` 0 ) = (/)')], 'coeq2i', '( inclBool o. ( encodeNat ` 0 ) ) = ( inclBool o. (/) )')
    g2 = w.s([], 'co02', '( inclBool o. (/) ) = (/)')
    g3 = w.s([g0, g1, g2], '3eqtri', '( encNatGam ` 0 ) = (/)')
    e4 = w.s([g3], 'oveq1i', '( ( encNatGam ` 0 ) ++ <" 4 "> ) = ( (/) ++ <" 4 "> )')
    e5 = w.s([w.s([w.s([], 'gamma4', "4 e. Gamma'"), w.inst('s1cl')], 'ax-mp', "<\" 4 \"> e. Word Gamma'"), w.inst('ccatlid')], 'ax-mp', '( (/) ++ <" 4 "> ) = <" 4 ">')
    e6 = w.s([e2, e3, e4], '3eqtri', '( encodeOutput ` <. 0 , (/) >. ) = ( (/) ++ <" 4 "> )')
    e7 = w.s([e6, e5], 'eqtri', '( encodeOutput ` <. 0 , (/) >. ) = <" 4 ">')
    eo = P([e1, P([e7], 'a1i' if False else 'a1i', '') if False else w.s([e7], 'a1i', '( %s -> ( encodeOutput ` <. 0 , (/) >. ) = <" 4 "> )' % ps)], 'eqtrd', '( encodeOutput ` ( %s ` N ) ) = <" 4 ">' % FM)
    ei = P([eo], 'fveq2d', '( inl ` ( encodeOutput ` ( %s ` N ) ) ) = ( inl ` <" 4 "> )' % FM)
    small = P([cs, ei], 'breqtrrd', OUT)
    # big inputs
    pb = '( %s /\\ -. N < ; 1 6 )' % ph
    B = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (pb, f))
    subb = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (pb, f))
    nl = B([], 'simpr', '-. N < ; 1 6')
    nr = B([subb(nn, 'N e. NN0')], 'nn0red', 'N e. RR')
    r16 = B([num.re_nat(w, 16)], 'a1i', '; 1 6 e. RR')
    lnl = B([r16, nr, w.inst('lenlt')], 'syl2anc', '( ; 1 6 <_ N <-> -. N < ; 1 6 )')
    le = B([nl, lnl], 'mpbird', '; 1 6 <_ N')
    z16 = B([w.s([num.nn0(w, 16)], 'nn0zi', '; 1 6 e. ZZ')], 'a1i', '; 1 6 e. ZZ')
    nz = B([subb(nn, 'N e. NN0')], 'nn0zd', 'N e. ZZ')
    nu = B([B([z16, nz, w.inst('eluz')], 'syl2anc', '( N e. ( ZZ>= ` ; 1 6 ) <-> ; 1 6 <_ N )'), le], 'mpbird' if False else 'mpbird', '') if False else None
    ez = B([z16, nz, w.inst('eluz')], 'syl2anc', '( N e. ( ZZ>= ` ; 1 6 ) <-> ; 1 6 <_ N )')
    nu = B([le, ez], 'mpbird', 'N e. ( ZZ>= ` ; 1 6 )')
    RB = '( ( %s + %s ) + 1 )' % (BPRE, SB)
    gb = B([subb(gv, '( %s ` N ) = %s' % (GM, GV)), B([nl], 'iffalsed', '%s = %s' % (GV, RB))], 'eqtrd', '( %s ` N ) = %s' % (GM, RB))
    rqb = B([gb, subb(gq, '( %s ` N ) <_ Q' % GM)], 'eqbrtrrd', '%s <_ Q' % RB)
    Lb = {'( ( C e. NN0 /\\ 1 <_ C ) /\\ K e. NN )': B([subb(c1, '( C e. NN0 /\\ 1 <_ C )'), subb(kn, 'K e. NN')], 'jca', '( ( C e. NN0 /\\ 1 <_ C ) /\\ K e. NN )'),
          'N e. ( ZZ>= ` ; 1 6 )': nu}
    rb, frb = use(w, pb, 't15runb', {}, Lb)
    sc = B([subb(c1, '( C e. NN0 /\\ 1 <_ C )'), subb(kn, 'K e. NN'), nu, w.inst('sctm16')], 'syl3anc', '( %s e. Scales /\\ 1 <_ ( 1st ` ( 1st ` ( 1st ` %s ) ) ) )' % (SCN, SCN))
    gd = B([B([sc], 'simpld', '%s e. Scales' % SCN), subb(nn, 'N e. NN0'), w.inst('srchgetd')], 'syl2anc', '%s e. ( NN0 X. Word NN0 )' % GETD)
    gg1 = B([gd, w.inst('xp1st')], 'syl', '( 1st ` %s ) e. NN0' % GETD)
    gg2 = B([gd, w.inst('xp2nd')], 'syl', '( 2nd ` %s ) e. Word NN0' % GETD)
    eg = B([gg1, gg2, w.inst('encoutcl')], 'syl2anc', "%s e. Word Gamma'" % ENC)
    Lc = {'( C e. NN0 /\\ K e. NN )': subb(ck, '( C e. NN0 /\\ K e. NN )'), 'N e. NN0': subb(nn, 'N e. NN0'), 'Q e. NN0': subb(qn, 'Q e. NN0'),
          "%s e. Word Gamma'" % ENC: eg, '%s <_ Q' % RB: rqb, frb: rb}
    cb, fcb = use(w, pb, 't15conv', {'O': ENC, 'R': RB}, Lc)
    fb = B([subb(fv, '( %s ` N ) = %s' % (FM, FV)), B([nl], 'iffalsed', '%s = %s' % (FV, GETD))], 'eqtrd', '( %s ` N ) = %s' % (FM, GETD))
    op = B([gd, w.inst('1st2nd2')], 'syl', '%s = <. ( 1st ` %s ) , ( 2nd ` %s ) >.' % (GETD, GETD, GETD))
    f2 = B([fb, op], 'eqtrd', '( %s ` N ) = <. ( 1st ` %s ) , ( 2nd ` %s ) >.' % (FM, GETD, GETD))
    e1b = B([f2], 'fveq2d', '( encodeOutput ` ( %s ` N ) ) = ( encodeOutput ` <. ( 1st ` %s ) , ( 2nd ` %s ) >. )' % (FM, GETD, GETD))
    e2b = B([w.s([], 'encoutfv', '( encodeOutput ` <. ( 1st ` %s ) , ( 2nd ` %s ) >. ) = %s' % (GETD, GETD, ENC))], 'a1i', '( encodeOutput ` <. ( 1st ` %s ) , ( 2nd ` %s ) >. ) = %s' % (GETD, GETD, ENC))
    eob = B([e1b, e2b], 'eqtrd', '( encodeOutput ` ( %s ` N ) ) = %s' % (FM, ENC))
    eib = B([eob], 'fveq2d', '( inl ` ( encodeOutput ` ( %s ` N ) ) ) = ( inl ` %s )' % (FM, ENC))
    big = B([cb, eib], 'breqtrrd', OUT)
    w.qed([small, big], 'pm2.61dan', '( %s -> %s )' % (ph, OUT))
    return w


GENS['t15out'] = t15out



def xge16(w, ante, xn, lt_neg):
    """( ante -> x e. ( ZZ>= ` ; 1 6 ) ) from ( ante -> x e. NN0 ), ( ante -> -. x < ; 1 6 )"""
    S = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (ante, f))
    xr = S([xn], 'nn0red', 'x e. RR')
    r16 = S([num.re_nat(w, 16)], 'a1i', '; 1 6 e. RR')
    le = S([lt_neg, S([r16, xr, w.inst('lenlt')], 'syl2anc', '( ; 1 6 <_ x <-> -. x < ; 1 6 )')], 'mpbird', '; 1 6 <_ x')
    z16 = S([w.s([num.nn0(w, 16)], 'nn0zi', '; 1 6 e. ZZ')], 'a1i', '; 1 6 e. ZZ')
    ez = S([z16, S([xn], 'nn0zd', 'x e. ZZ'), w.inst('eluz')], 'syl2anc', '( x e. ( ZZ>= ` ; 1 6 ) <-> ; 1 6 <_ x )')
    return S([le, ez], 'mpbird', 'x e. ( ZZ>= ` ; 1 6 )')


def t15gty():
    w = W('t15gty', 'The step function g of the concrete machine is a function to NN0.')
    ph = '( ( C e. NN0 /\\ 1 <_ C ) /\\ K e. NN )'
    px = '( %s /\\ x e. NN0 )' % ph
    X = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (px, f))
    xn = X([], 'simpr', 'x e. NN0')
    Bx = tx(BPRE)
    ps = '( %s /\\ x < ; 1 6 )' % px
    zx = w.s([w.s([xn], 'adantr', '( %s -> x e. NN0 )' % ps), w.inst('encnatcl')], 'syl', '( %s -> ( encodeNat ` x ) e. Word 2o )' % ps)
    zl = w.s([zx, w.inst('lencl')], 'syl', '( %s -> ( # ` ( encodeNat ` x ) ) e. NN0 )' % ps)
    b1 = w.s([w.s([w.s([num.nn0(w, 7)], 'a1i', '( %s -> 7 e. NN0 )' % ps), zl], 'nn0mulcld', '( %s -> ( 7 x. ( # ` ( encodeNat ` x ) ) ) e. NN0 )' % ps),
              w.s([num.nn0(w, 70)], 'a1i', '( %s -> ; 7 0 e. NN0 )' % ps)], 'nn0addcld', '( %s -> %s e. NN0 )' % (ps, Bx))
    b2 = w.s([b1, w.s([w.s([], '1nn0', '1 e. NN0')], 'a1i', '( %s -> 1 e. NN0 )' % ps)], 'nn0addcld', '( %s -> ( %s + 1 ) e. NN0 )' % (ps, Bx))
    pb = '( %s /\\ -. x < ; 1 6 )' % px
    xnb = w.s([xn], 'adantr', '( %s -> x e. NN0 )' % pb)
    xu = xge16(w, pb, xnb, w.s([], 'simpr', '( %s -> -. x < ; 1 6 )' % pb))
    RB = '( ( %s + %s ) + 1 )' % (Bx, tx(SB))
    base = w.s([], 'simpll', '( %s -> %s )' % (pb, ph))
    fr = stmt_of('t15runb')
    A_, B_ = split_imp(fr)
    B2 = subst_text(B_, {'N': 'x'})
    rb = w.s([w.s([base, xu], 'jca', '( %s -> %s )' % (pb, subst_text(A_, {'N': 'x'}))), w.inst('t15runb')], 'syl', '( %s -> %s )' % (pb, B2))
    TY_ = '( TMTy C K )'; PG_ = '( TMProg C K )'
    tv = w.s([w.s([w.s([], 'df-tmty', '%s = <. <. TMGam , ( TMLbl C K ) >. , TMSt >.' % TY_), w.s([], 'opex', '<. <. TMGam , ( TMLbl C K ) >. , TMSt >. e. _V')], 'eqeltri', '%s e. _V' % TY_)], 'a1i', '( %s -> %s e. _V )' % (pb, TY_))
    cn = w.s([base], 'simpld', '( %s -> ( C e. NN0 /\\ 1 <_ C ) )' % pb)
    ck = w.s([w.s([cn], 'simpld', '( %s -> C e. NN0 )' % pb), w.s([base], 'simprd', '( %s -> K e. NN )' % pb)], 'jca', '( %s -> ( C e. NN0 /\\ K e. NN ) )' % pb)
    pg = w.s([ck, w.inst('t15prog')], 'syl', '( %s -> %s : ( 2nd ` ( 1st ` %s ) ) --> ( TM2Stmt ` %s ) )' % (pb, PG_, TY_, TY_))
    pv = w.s([pg, w.s([], 'fvexd', '( %s -> ( 2nd ` ( 1st ` %s ) ) e. _V )' % (pb, TY_)), w.inst('fex')], 'syl2anc', '( %s -> %s e. _V )' % (pb, PG_))
    import t15_g_pre as GP
    Cc, Pp, Nn = GP.parse_tri(B2.replace('( %s TM2Hoare %s )' % (TY_, PG_), '( T TM2Hoare M )'))
    ty = w.s([w.s([w.s([tv, pv], 'jca', '( %s -> ( %s e. _V /\\ %s e. _V ) )' % (pb, TY_, PG_)), rb], 'jca', '( %s -> ( ( %s e. _V /\\ %s e. _V ) /\\ %s ) )' % (pb, TY_, PG_, B2)), w.inst('tm2hrtyp')], 'syl',
             '( %s -> ( %s C_ ( TM2Cfg ` %s ) /\\ %s C_ ( TM2Cfg ` %s ) /\\ %s e. NN0 ) )' % (pb, Cc, TY_, Pp, TY_, Nn))
    assert Nn == RB, (Nn[:80], RB[:80])
    b3 = w.s([ty], 'simp3d', '( %s -> %s e. NN0 )' % (pb, RB))
    ic = X([b2, b3], 'ifclda', '%s e. NN0' % subst_text(GBODY, {}))
    w.qed([ic], 'fmptd', '( %s -> %s : NN0 --> NN0 )' % (ph, GM))
    return w


def t15fty():
    w = W('t15fty', 'The output function f of the concrete machine maps NN0 to pairs of a number and a word.')
    ph = '( ( C e. NN0 /\\ 1 <_ C ) /\\ K e. NN )'
    px = '( %s /\\ x e. NN0 )' % ph
    xn = w.s([], 'simpr', '( %s -> x e. NN0 )' % px)
    ps = '( %s /\\ x < ; 1 6 )' % px
    o = w.s([w.s([w.s([], '0nn0', '0 e. NN0'), w.s([], 'wrd0', '(/) e. Word NN0'), w.inst('opelxpi')], 'mp2an', '<. 0 , (/) >. e. ( NN0 X. Word NN0 )')], 'a1i', '( %s -> <. 0 , (/) >. e. ( NN0 X. Word NN0 ) )' % ps)
    pb = '( %s /\\ -. x < ; 1 6 )' % px
    xnb = w.s([xn], 'adantr', '( %s -> x e. NN0 )' % pb)
    xu = xge16(w, pb, xnb, w.s([], 'simpr', '( %s -> -. x < ; 1 6 )' % pb))
    base = w.s([], 'simpll', '( %s -> %s )' % (pb, ph))
    cn = w.s([base], 'simpld', '( %s -> ( C e. NN0 /\\ 1 <_ C ) )' % pb)
    kn = w.s([base], 'simprd', '( %s -> K e. NN )' % pb)
    SCx = '( ( C ScTM K ) ` x )'
    sc = w.s([cn, kn, xu, w.inst('sctm16')], 'syl3anc', '( %s -> ( %s e. Scales /\\ 1 <_ ( 1st ` ( 1st ` ( 1st ` %s ) ) ) ) )' % (pb, SCx, SCx))
    gd = w.s([w.s([sc], 'simpld', '( %s -> %s e. Scales )' % (pb, SCx)), xnb, w.inst('srchgetd')], 'syl2anc', '( %s -> %s e. ( NN0 X. Word NN0 ) )' % (pb, tx(GETD)))
    ic = w.s([o, gd], 'ifclda', '( %s -> %s e. ( NN0 X. Word NN0 ) )' % (px, FBODY))
    w.qed([ic], 'fmptd', '( %s -> %s : NN0 --> ( NN0 X. Word NN0 ) )' % (ph, FM))
    return w


GENS['t15gty'] = t15gty
GENS['t15fty'] = t15fty



I0 = "( _I |` Gamma' )"
HT = '<. %s , <. <. %s , %s >. , H >. >.' % (MACH, I0, I0)
ENCT = "<. <. encNatGam , Gamma' >. , <. encodeOutput , Gamma' >. , %s >." % FM


def t15comp():
    w = W('t15comp', 'The concrete machine computes f in time H whenever H bounds the step function g (Lean: exists_computableInTime).')
    HH = '( H : NN0 --> NN0 /\\ A. n e. NN0 ( %s ` n ) <_ ( H ` ( # ` ( encodeNat ` n ) ) ) )' % GM
    ph = '( ( ( C e. NN0 /\\ 1 <_ C ) /\\ K e. NN ) /\\ %s )' % HH
    S = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (ph, f))
    base = S([], 'simpl', '( ( C e. NN0 /\\ 1 <_ C ) /\\ K e. NN )')
    c1 = S([base], 'simpld', '( C e. NN0 /\\ 1 <_ C )')
    cn = S([c1], 'simpld', 'C e. NN0'); kn = S([base], 'simprd', 'K e. NN')
    ck = S([cn, kn], 'jca', '( C e. NN0 /\\ K e. NN )')
    hh = S([], 'simpr', HH)
    hf = S([hh], 'simpld', 'H : NN0 --> NN0')
    hb = S([hh], 'simprd', 'A. n e. NN0 ( %s ` n ) <_ ( H ` ( # ` ( encodeNat ` n ) ) )' % GM)
    mf = S([ck, w.inst('t15mfin')], 'syl', '%s e. FinTM2' % MACH)
    # sets
    mv = S([mf], 'elexd', '%s e. _V' % MACH)
    iv = S([w.s([w.s([], 'gammaex', "Gamma' e. _V"), w.inst('resiexg')], 'ax-mp', '%s e. _V' % I0)], 'a1i', '%s e. _V' % I0)
    n0x = S([w.s([], 'nn0ex', 'NN0 e. _V')], 'a1i', 'NN0 e. _V')
    hv = S([hf, n0x, w.inst('fex')], 'syl2anc', 'H e. _V')
    ev = S([w.s([w.s([], 'encnatgamf', "encNatGam : NN0 --> Word Gamma'"), w.s([], 'nn0ex', 'NN0 e. _V'), w.inst('fex')], 'mp2an', 'encNatGam e. _V')], 'a1i', 'encNatGam e. _V')
    gx = S([w.s([], 'gammaex', "Gamma' e. _V")], 'a1i', "Gamma' e. _V")
    xw = w.s([w.s([], 'nn0ex', 'NN0 e. _V'), w.s([w.s([], 'nn0ex', 'NN0 e. _V'), w.inst('wrdexg')], 'ax-mp', 'Word NN0 e. _V')], 'xpex', '( NN0 X. Word NN0 ) e. _V')
    ox = S([w.s([w.s([], 'encoutf', "encodeOutput : ( NN0 X. Word NN0 ) --> Word Gamma'"), xw, w.inst('fex')], 'mp2an', 'encodeOutput e. _V')], 'a1i', 'encodeOutput e. _V')
    fx = S([w.s([w.s([], 'nn0ex', 'NN0 e. _V')], 'mptex', '%s e. _V' % FM)], 'a1i', '%s e. _V' % FM)
    L = {'%s e. _V' % MACH: mv, '%s e. _V' % I0: iv, 'H e. _V': hv, 'encNatGam e. _V': ev, "Gamma' e. _V": gx,
         'encodeOutput e. _V': ox, '%s e. _V' % FM: fx}
    # projections
    pj = w.s([], 't15mproj', stmt_of('t15mproj'))
    pcx = w.s([pj], 'simp3i', subst_text(and_parts(stmt_of('t15mproj'))[2], {}))
    p5, p6, p7 = and_parts(and_parts(stmt_of('t15mproj'))[2])
    e5 = w.s([pcx], 'simp1i', p5); e6 = w.s([pcx], 'simp2i', p6); e7 = w.s([pcx], 'simp3i', p7)
    G0 = '( ( 1st ` ( 1st ` ( 1st ` ( 1st ` %s ) ) ) ) ` ( 1st ` ( 2nd ` ( 1st ` %s ) ) ) )' % (MACH, MACH)
    G1_ = '( ( 1st ` ( 1st ` ( 1st ` ( 1st ` %s ) ) ) ) ` ( 2nd ` ( 2nd ` ( 1st ` %s ) ) ) )' % (MACH, MACH)
    q0 = w.s([e5, e6], 'fveq12i', '%s = ( TMGam ` 0 )' % G0)
    q1 = w.s([e5, e7], 'fveq12i', '%s = ( TMGam ` 1 )' % G1_)

    def in8(k):
        a = num.nn0(w, k); bb = w.s([], '8nn', '8 e. NN'); c = num.le_nat(w, k, 8, strict=True)
        e = w.s([], 'elfzo0', '( %d e. ( 0 ..^ 8 ) <-> ( %d e. NN0 /\\ 8 e. NN /\\ %d < 8 ) )' % (k, k, k))
        return w.s([a, bb, c, e], 'mpbir3an', '%d e. ( 0 ..^ 8 )' % k)
    r0 = w.s([q0, w.s([in8(0), w.inst('tmgamfv')], 'ax-mp', "( TMGam ` 0 ) = Gamma'")], 'eqtri', "%s = Gamma'" % G0)
    r1 = w.s([q1, w.s([in8(1), w.inst('tmgamfv')], 'ax-mp', "( TMGam ` 1 ) = Gamma'")], 'eqtri', "%s = Gamma'" % G1_)
    fi = w.s([], 'f1oi', "%s : Gamma' -1-1-onto-> Gamma'" % I0)
    i0 = w.s([fi, w.s([r0, w.inst('f1oeq2')], 'ax-mp', "( %s : %s -1-1-onto-> Gamma' <-> %s : Gamma' -1-1-onto-> Gamma' )" % (I0, G0, I0))], 'mpbir', "%s : %s -1-1-onto-> Gamma'" % (I0, G0))
    i1 = w.s([fi, w.s([r1, w.inst('f1oeq2')], 'ax-mp', "( %s : %s -1-1-onto-> Gamma' <-> %s : Gamma' -1-1-onto-> Gamma' )" % (I0, G1_, I0))], 'mpbir', "%s : %s -1-1-onto-> Gamma'" % (I0, G1_))
    L['%s e. FinTM2' % MACH] = mf
    L["%s : %s -1-1-onto-> Gamma'" % (I0, G0)] = S([i0], 'a1i', "%s : %s -1-1-onto-> Gamma'" % (I0, G0))
    L["%s : %s -1-1-onto-> Gamma'" % (I0, G1_)] = S([i1], 'a1i', "%s : %s -1-1-onto-> Gamma'" % (I0, G1_))
    L['H : NN0 --> NN0'] = hf
    # the outputs
    pa = '( %s /\\ a e. NN0 )' % ph
    A = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (pa, f))
    sub = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (pa, f))
    am = A([], 'simpr', 'a e. NN0')
    eg = A([am, w.inst('encnatgamcl')], 'syl', "( encNatGam ` a ) e. Word Gamma'")
    el = A([am, w.inst('encnatgamlen')], 'syl', '( # ` ( encNatGam ` a ) ) = ( # ` ( encodeNat ` a ) )')
    ln = A([A([am, w.inst('encnatcl')], 'syl', '( encodeNat ` a ) e. Word 2o'), w.inst('lencl')], 'syl', '( # ` ( encodeNat ` a ) ) e. NN0')
    qn = A([sub(hf, 'H : NN0 --> NN0'), ln], 'ffvelcdmd', '( H ` ( # ` ( encodeNat ` a ) ) ) e. NN0')
    cq = w.s([w.s([], 'fveq2', '( n = a -> ( %s ` n ) = ( %s ` a ) )' % (GM, GM)),
              w.s([w.s([w.s([w.s([], 'fveq2', '( n = a -> ( encodeNat ` n ) = ( encodeNat ` a ) )')], 'fveq2d', '( n = a -> ( # ` ( encodeNat ` n ) ) = ( # ` ( encodeNat ` a ) ) )')], 'fveq2d',
                   '( n = a -> ( H ` ( # ` ( encodeNat ` n ) ) ) = ( H ` ( # ` ( encodeNat ` a ) ) ) )')], 'id', '') if False else
              w.s([w.s([w.s([], 'fveq2', '( n = a -> ( encodeNat ` n ) = ( encodeNat ` a ) )')], 'fveq2d', '( n = a -> ( # ` ( encodeNat ` n ) ) = ( # ` ( encodeNat ` a ) ) )')], 'fveq2d',
                  '( n = a -> ( H ` ( # ` ( encodeNat ` n ) ) ) = ( H ` ( # ` ( encodeNat ` a ) ) ) )')], 'breq12d',
             '( n = a -> ( ( %s ` n ) <_ ( H ` ( # ` ( encodeNat ` n ) ) ) <-> ( %s ` a ) <_ ( H ` ( # ` ( encodeNat ` a ) ) ) ) )' % (GM, GM))
    rs = w.s([cq], 'rspcv', '( a e. NN0 -> ( A. n e. NN0 ( %s ` n ) <_ ( H ` ( # ` ( encodeNat ` n ) ) ) -> ( %s ` a ) <_ ( H ` ( # ` ( encodeNat ` a ) ) ) ) )' % (GM, GM))
    gq = A([am, sub(hb, 'A. n e. NN0 ( %s ` n ) <_ ( H ` ( # ` ( encodeNat ` n ) ) )' % GM), rs], 'sylc', '( %s ` a ) <_ ( H ` ( # ` ( encodeNat ` a ) ) )' % GM)
    Q = '( H ` ( # ` ( encodeNat ` a ) ) )'
    Lo = {'( ( C e. NN0 /\\ 1 <_ C ) /\\ K e. NN )': sub(base, '( ( C e. NN0 /\\ 1 <_ C ) /\\ K e. NN )'), 'a e. NN0': am, '%s e. NN0' % Q: qn,
          '( %s ` a ) <_ %s' % (GM, Q): gq}
    ou, fou = use(w, pa, 't15out', {'N': 'a', 'Q': Q}, Lo)
    # rewrite into tm2comptel's form
    ci = w.s([], 'cnvresid', "`' %s = %s" % (I0, I0))
    fa = A([eg, w.inst('wrdf')], 'syl', "( encNatGam ` a ) : ( 0 ..^ ( # ` ( encNatGam ` a ) ) ) --> Gamma'")
    x1 = A([A([ci], 'a1i', "`' %s = %s" % (I0, I0))], 'coeq1d', "( `' %s o. ( encNatGam ` a ) ) = ( %s o. ( encNatGam ` a ) )" % (I0, I0))
    x2 = A([fa, w.inst('fcoi2')], 'syl', "( %s o. ( encNatGam ` a ) ) = ( encNatGam ` a )" % I0)
    X1 = A([x1, x2], 'eqtrd', "( `' %s o. ( encNatGam ` a ) ) = ( encNatGam ` a )" % I0)
    ft = A([sub(S([base, w.inst('t15fty')], 'syl', '%s : NN0 --> ( NN0 X. Word NN0 )' % FM), '%s : NN0 --> ( NN0 X. Word NN0 )' % FM), am], 'ffvelcdmd', '( %s ` a ) e. ( NN0 X. Word NN0 )' % FM)
    eo = A([A([w.s([], 'encoutf', "encodeOutput : ( NN0 X. Word NN0 ) --> Word Gamma'")], 'a1i', "encodeOutput : ( NN0 X. Word NN0 ) --> Word Gamma'"), ft], 'ffvelcdmd', "( encodeOutput ` ( %s ` a ) ) e. Word Gamma'" % FM)
    fo = A([eo, w.inst('wrdf')], 'syl', "( encodeOutput ` ( %s ` a ) ) : ( 0 ..^ ( # ` ( encodeOutput ` ( %s ` a ) ) ) ) --> Gamma'" % (FM, FM))
    y1 = A([A([ci], 'a1i', "`' %s = %s" % (I0, I0))], 'coeq1d', "( `' %s o. ( encodeOutput ` ( %s ` a ) ) ) = ( %s o. ( encodeOutput ` ( %s ` a ) ) )" % (I0, FM, I0, FM))
    y2 = A([fo, w.inst('fcoi2')], 'syl', "( %s o. ( encodeOutput ` ( %s ` a ) ) ) = ( encodeOutput ` ( %s ` a ) )" % (I0, FM, FM))
    Y1 = A([y1, y2], 'eqtrd', "( `' %s o. ( encodeOutput ` ( %s ` a ) ) ) = ( encodeOutput ` ( %s ` a ) )" % (I0, FM, FM))
    Y2 = A([Y1], 'fveq2d', "( inl ` ( `' %s o. ( encodeOutput ` ( %s ` a ) ) ) ) = ( inl ` ( encodeOutput ` ( %s ` a ) ) )" % (I0, FM, FM))
    R1 = A([A([el], 'fveq2d', '( H ` ( # ` ( encNatGam ` a ) ) ) = %s' % Q)], 'oveq2d', '( %s TM2OutputsInTime ( H ` ( # ` ( encNatGam ` a ) ) ) ) = ( %s TM2OutputsInTime %s )' % (MACH, MACH, Q))
    TGT = "( `' %s o. ( encNatGam ` a ) ) ( %s TM2OutputsInTime ( H ` ( # ` ( encNatGam ` a ) ) ) ) ( inl ` ( `' %s o. ( encodeOutput ` ( %s ` a ) ) ) )" % (I0, MACH, I0, FM)
    bq = A([X1, R1, Y2], 'breq123d', '( %s <-> %s )' % (TGT, fou))
    one = A([ou, bq], 'mpbird', TGT)
    al = S([one], 'ralrimiva', 'A. a e. NN0 %s' % TGT)
    dq = w.s([w.s([], 'encnatgamf', "encNatGam : NN0 --> Word Gamma'"), w.inst('fdm')], 'ax-mp', 'dom encNatGam = NN0')
    al2 = S([al, S([w.s([dq], 'raleqi', '( A. a e. dom encNatGam %s <-> A. a e. NN0 %s )' % (TGT, TGT))], 'a1i', '( A. a e. dom encNatGam %s <-> A. a e. NN0 %s )' % (TGT, TGT))], 'mpbird', 'A. a e. dom encNatGam %s' % TGT)
    L['A. a e. dom encNatGam %s' % TGT] = al2
    A_, B_ = split_imp(stmt_of('tm2comptel'))
    m = {'M': MACH, 'I': I0, 'J': I0, 'T': 'H', 'D': 'encNatGam', 'A': "Gamma'", 'G': 'encodeOutput', 'B': "Gamma'", 'F': FM,
         'P': '_V', 'Q': '_V', 'R': '_V', 'U': '_V', 'V': '_V', 'W': '_V', 'X': '_V', 'Y': '_V', 'Z': '_V'}
    A2, B2 = subst_text(A_, m), subst_text(B_, m)
    lhs, rhs = B2[2:-2].split(' <-> ', 1) if False else (None, None)
    ce = w.s([build_conj(w, ph, A2, L), w.inst('tm2comptel')], 'syl', '( %s -> %s )' % (ph, B2))
    # B2 = ( LHS <-> RHS )
    toks = B2.split()[1:-1]
    d = 0
    for q, x in enumerate(toks):
        if x in OPEN: d += 1
        elif x in CLOSE: d -= 1
        elif d == 0 and x == '<->': break
    LHS, RHS = ' '.join(toks[:q]), ' '.join(toks[q + 1:])
    rr = build_conj(w, ph, RHS, L)
    got = S([rr, ce], 'mpbird', LHS)
    ot = w.s([], 'df-ot', "<. <. encNatGam , Gamma' >. , <. encodeOutput , Gamma' >. , %s >. = <. <. <. encNatGam , Gamma' >. , <. encodeOutput , Gamma' >. >. , %s >." % (FM, FM))
    w.qed([got, S([ot], 'a1i', ot and "%s = <. <. <. encNatGam , Gamma' >. , <. encodeOutput , Gamma' >. >. , %s >." % (ENCT, FM))], 'breqtrrd', '( %s -> %s TM2CompT %s )' % (ph, HT, ENCT))
    return w


GENS['t15comp'] = t15comp



COST = 'E. m e. NN0 A. n e. ( ZZ>= ` m ) ( 2nd ` ( ( ( C ScTM K ) ` n ) Search n ) ) <_ ( exp ` ( ( ; ; 1 0 0 x. ( ell2 ` n ) ) x. ( ell3 ` n ) ) )'
Mn = '( ( ell2 ` n ) x. ( ell3 ` n ) )'
CHI = '( 1 <_ ( ell2 ` n ) /\\ ( %s ` n ) <_ ( exp ` ( ; ; ; 2 0 0 1 x. %s ) ) )' % (GM, Mn)


def t15gev():
    w = W('t15gev', 'Eventually the step function g of the concrete machine is at most exp ( 2001 ell2 n ell3 n ) (Lean: searchBound_ExpB with the prefix of route beta).')
    base = '( ( C e. NN0 /\\ ; ; ; 1 0 0 0 <_ C ) /\\ K e. NN )'
    ph = '( %s /\\ %s )' % (base, COST)
    A_, B_ = split_imp(stmt_of('sbexpbev'))
    assert A_ == ph, A_[:100]
    E1 = B_
    PSI1 = E1[len('E. m e. NN0 A. n e. ( ZZ>= ` m ) '):]
    e1 = w.s([w.inst('sbexpbev')], 'id', '') if False else w.s([], 'sbexpbev', '( %s -> %s )' % (ph, E1))
    e2 = w.s([w.s([], '1re', '1 e. RR'), w.inst('ell3ge')], 'ax-mp', 'E. m e. NN0 A. n e. ( ZZ>= ` m ) 1 <_ ( ell3 ` n )')
    s1 = w.s([], 'id', '( n e. ( ZZ>= ` ; 1 6 ) -> n e. ( ZZ>= ` ; 1 6 ) )')
    s2 = w.s([s1], 'rgen', 'A. n e. ( ZZ>= ` ; 1 6 ) n e. ( ZZ>= ` ; 1 6 )')
    c1 = w.s([w.s([w.s([], 'id', '( m = ; 1 6 -> m = ; 1 6 )')], 'fveq2d', '( m = ; 1 6 -> ( ZZ>= ` m ) = ( ZZ>= ` ; 1 6 ) )')], 'raleqdv',
             '( m = ; 1 6 -> ( A. n e. ( ZZ>= ` m ) n e. ( ZZ>= ` ; 1 6 ) <-> A. n e. ( ZZ>= ` ; 1 6 ) n e. ( ZZ>= ` ; 1 6 ) ) )')
    e3 = w.s([num.nn0(w, 16), s2, w.s([c1], 'rspcev', '( ( ; 1 6 e. NN0 /\\ A. n e. ( ZZ>= ` ; 1 6 ) n e. ( ZZ>= ` ; 1 6 ) ) -> E. m e. NN0 A. n e. ( ZZ>= ` m ) n e. ( ZZ>= ` ; 1 6 ) )')], 'mp2an',
             'E. m e. NN0 A. n e. ( ZZ>= ` m ) n e. ( ZZ>= ` ; 1 6 )')
    PSI = '( ( %s /\\ 1 <_ ( ell3 ` n ) ) /\\ n e. ( ZZ>= ` ; 1 6 ) )' % PSI1
    E12 = 'E. m e. NN0 A. n e. ( ZZ>= ` m ) ( %s /\\ 1 <_ ( ell3 ` n ) )' % PSI1
    a12 = w.s([e1, w.s([e2], 'a1i', '( %s -> E. m e. NN0 A. n e. ( ZZ>= ` m ) 1 <_ ( ell3 ` n ) )' % ph), w.inst('extrwevan')], 'syl2anc', '( %s -> %s )' % (ph, E12))
    a123 = w.s([a12, w.s([e3], 'a1i', '( %s -> E. m e. NN0 A. n e. ( ZZ>= ` m ) n e. ( ZZ>= ` ; 1 6 ) )' % ph), w.inst('extrwevan')], 'syl2anc',
               '( %s -> E. m e. NN0 A. n e. ( ZZ>= ` m ) %s )' % (ph, PSI))
    # pointwise, under the n-free base
    pn = '( ( %s /\\ n e. NN0 ) /\\ %s )' % (base, PSI)
    P = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (pn, f))
    nn = P([], 'simplr', 'n e. NN0')
    ps = P([], 'simpr', PSI)
    p1 = P([ps], 'simpld', '( %s /\\ 1 <_ ( ell3 ` n ) )' % PSI1)
    a1_ = P([p1], 'simpld', PSI1)
    l3 = P([p1], 'simprd', '1 <_ ( ell3 ` n )')
    nu = P([ps], 'simprd', 'n e. ( ZZ>= ` ; 1 6 )')
    l2 = P([a1_], 'simp1d', '1 <_ ( ell2 ` n )')
    lm = P([a1_], 'simp2d', '; ; ; 2 4 0 0 <_ %s' % Mn)
    lsb = P([a1_], 'simp3d', '( %s + 1 ) <_ ( exp ` ( ; ; ; 2 0 0 0 x. %s ) )' % (subst_text(SB, {'N': 'n'}), Mn))
    bs = P([], 'simpll', base)
    cc = P([bs], 'simpld', '( C e. NN0 /\\ ; ; ; 1 0 0 0 <_ C )')
    cn = P([cc], 'simpld', 'C e. NN0')
    cr = P([cn], 'nn0red', 'C e. RR')
    c1k = linarith(w, pn, [P([cc], 'simprd', '; ; ; 1 0 0 0 <_ C')], '1 <_ C', leaves={'C': cr})
    kn = P([bs], 'simprd', 'K e. NN')
    zb = P([P([nu, P([l2, l3, lm], '3jca', '( 1 <_ ( ell2 ` n ) /\\ 1 <_ ( ell3 ` n ) /\\ ; ; ; 2 4 0 0 <_ %s )' % Mn)], 'jca',
              '( n e. ( ZZ>= ` ; 1 6 ) /\\ ( 1 <_ ( ell2 ` n ) /\\ 1 <_ ( ell3 ` n ) /\\ ; ; ; 2 4 0 0 <_ %s ) )' % Mn), w.inst('t15zb')], 'syl',
           '%s <_ ( exp ` ( 2 x. %s ) )' % (subst_text(BPRE, {'N': 'n'}), Mn))
    SBn = subst_text(SB, {'N': 'n'})
    BPn = subst_text(BPRE, {'N': 'n'})
    sbn = P([P([P([P([cn, c1k], 'jca', '( C e. NN0 /\\ 1 <_ C )'), kn], 'jca', '( ( C e. NN0 /\\ 1 <_ C ) /\\ K e. NN )'), nu], 'jca',
               '( ( ( C e. NN0 /\\ 1 <_ C ) /\\ K e. NN ) /\\ n e. ( ZZ>= ` ; 1 6 ) )'), w.inst('t15sbcl')], 'syl', '%s e. NN0' % SBn)
    zn = P([P([nn, w.inst('encnatcl')], 'syl', '( encodeNat ` n ) e. Word 2o'), w.inst('lencl')], 'syl', '( # ` ( encodeNat ` n ) ) e. NN0')
    bpn = P([P([P([num.nn0(w, 7)], 'a1i', '7 e. NN0'), zn], 'nn0mulcld', '( 7 x. ( # ` ( encodeNat ` n ) ) ) e. NN0'), P([num.nn0(w, 70)], 'a1i', '; 7 0 e. NN0')], 'nn0addcld', '%s e. NN0' % BPn)
    one0 = P([w.s([], '1nn0', '1 e. NN0')], 'a1i', '1 e. NN0')
    sb1 = P([sbn, one0], 'nn0addcld', '( %s + 1 ) e. NN0' % SBn)
    as_ = P([P([bpn], 'nn0cnd', '%s e. CC' % BPn), P([sbn], 'nn0cnd', '%s e. CC' % SBn), P([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '1 e. CC')], 'addassd',
            '( ( %s + %s ) + 1 ) = ( %s + ( %s + 1 ) )' % (BPn, SBn, BPn, SBn))
    def uzk(k):
        kz = P([w.s([num.nn0(w, k)], 'nn0zi', '%d e. ZZ' % k)], 'a1i', '%d e. ZZ' % k)
        kl = P([num.le_nat(w, k, 16)], 'a1i', '%d <_ ; 1 6' % k)
        im = P([kz, kl, w.inst('eluzuzle')], 'syl2anc', '( n e. ( ZZ>= ` ; 1 6 ) -> n e. ( ZZ>= ` %d ) )' % k)
        return P([nu, im], 'mpd', 'n e. ( ZZ>= ` %d )' % k)
    e2r = P([uzk(2), w.inst('ell2cl')], 'syl', '( ell2 ` n ) e. RR')
    e3r = P([uzk(3), w.inst('ell3cl')], 'syl', '( ell3 ` n ) e. RR')
    mr = P([e2r, e3r], 'remulcld', '%s e. RR' % Mn)
    m1 = linarith(w, pn, [lm], '1 <_ %s' % Mn, leaves={Mn: mr})
    L = {}
    def rl(n_):
        return P([num.re_nat(w, n_)], 'a1i', '%s e. RR' % num_text(n_))
    hy = [mr, m1, rl(2), rl(2000), rl(2000), rl(2001),
          P([num.le_nat(w, 2, 2000)], 'a1i', '2 <_ ; ; ; 2 0 0 0'),
          P([num.le_nat(w, 2000, 2000)], 'a1i', '; ; ; 2 0 0 0 <_ ; ; ; 2 0 0 0'),
          P([w.s([num.add_nat(w, 2000, 1), num.le_nat(w, 2001, 2001)], 'eqbrtri', '( ; ; ; 2 0 0 0 + 1 ) <_ ; ; ; 2 0 0 1')], 'a1i', '( ; ; ; 2 0 0 0 + 1 ) <_ ; ; ; 2 0 0 1'),
          P([bpn], 'nn0red', '%s e. RR' % BPn), P([sb1], 'nn0red', '( %s + 1 ) e. RR' % SBn), zb, lsb]
    xa = P(hy, 'xbadd', '( %s + ( %s + 1 ) ) <_ ( exp ` ( ; ; ; 2 0 0 1 x. %s ) )' % (BPn, SBn, Mn))
    GVn = subst_text(GBODY, {'x': 'n'})
    gv, _ = fvm(w, pn, GM, None, 'x', 'NN0', GBODY, 'n', nn, P([w.s([], 'ifex', '%s e. _V' % GVn)], 'a1i', '%s e. _V' % GVn))
    nr = P([nn], 'nn0red', 'n e. RR')
    r16 = P([num.re_nat(w, 16)], 'a1i', '; 1 6 e. RR')
    le16 = P([nu, w.inst('eluzle')], 'syl', '; 1 6 <_ n')
    nlt = P([le16, P([r16, nr, w.inst('lenlt')], 'syl2anc', '( ; 1 6 <_ n <-> -. n < ; 1 6 )')], 'mpbid', '-. n < ; 1 6')
    gb = P([gv, P([nlt], 'iffalsed', '%s = ( ( %s + %s ) + 1 )' % (GVn, BPn, SBn))], 'eqtrd', '( %s ` n ) = ( ( %s + %s ) + 1 )' % (GM, BPn, SBn))
    g2 = P([gb, as_], 'eqtrd', '( %s ` n ) = ( %s + ( %s + 1 ) )' % (GM, BPn, SBn))
    gq = P([g2, xa], 'eqbrtrd', '( %s ` n ) <_ ( exp ` ( ; ; ; 2 0 0 1 x. %s ) )' % (GM, Mn))
    ch = P([l2, gq], 'jca', CHI)
    im = w.s([ch], 'ex', '( ( %s /\\ n e. NN0 ) -> ( %s -> %s ) )' % (base, PSI, CHI))
    al = w.s([im], 'ralrimiva', '( %s -> A. n e. NN0 ( %s -> %s ) )' % (base, PSI, CHI))
    ala = w.s([al], 'adantr', '( %s -> A. n e. NN0 ( %s -> %s ) )' % (ph, PSI, CHI))
    w.qed([a123, ala, w.inst('extrwevim')], 'syl2anc', '( %s -> E. m e. NN0 A. n e. ( ZZ>= ` m ) %s )' % (ph, CHI))
    return w


GENS['t15gev'] = t15gev




BODYW = split_imp(stmt_of('carmswn'))[1][len('E. c e. NN0 E. k e. NN '):]
_fr = open(os.path.join(ROOT, 'scratch', 'carmtm.mmp')).read()
GTXT = ' '.join(_fr[_fr.index('qed::') + 5:].split('$)')[0].split()[1:])
SUCC0 = and_parts(and_parts(BODYW)[1])[1]              # A. e e. RR ( 0 < e -> E. m e. NN0 A. n e. ( ZZ>= ` m ) SUCCB )
SUCCB0 = SUCC0[len('A. e e. RR ( 0 < e -> E. m e. NN0 A. n e. ( ZZ>= ` m ) '):-2]
SUCCB = subst_text(SUCCB0, {'c': 'C', 'k': 'K'})
# carmtm's correctness clause and its body
_g2 = and_parts(GTXT[len('E. f '):])
_gh = _g2[1][len('E. h '):]
_gh2 = and_parts(_gh)
TIMEC, CORRC = and_parts(_gh2[1])
PROPSf = CORRC[len('A. e e. RR+ E. m e. NN0 A. n e. ( ZZ>= ` m ) '):]


def t15corr():
    w = W('t15corr', 'At an input n >= 16 where the search succeeds, the output f n of the concrete machine is a Carmichael number with its factorization (carmtm correctness clause, pointwise).')
    base = '( ( C e. NN0 /\\ 1 <_ C ) /\\ K e. NN )'
    ph = '( ( %s /\\ n e. ( ZZ>= ` ; 1 6 ) ) /\\ %s )' % (base, SUCCB)
    S = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (ph, f))
    bs = S([], 'simpll', base)
    nu = S([], 'simplr', 'n e. ( ZZ>= ` ; 1 6 )')
    sb = S([], 'simpr', SUCCB)
    sp = and_parts(SUCCB)
    ne = S([sb], 'simpld', sp[0])
    p2 = S([sb], 'simprd', sp[1])
    nn = S([S([num.nn0(w, 16)], 'a1i', '; 1 6 e. NN0'), nu, w.inst('eluznn0')], 'syl2anc', 'n e. NN0')
    nr = S([nn], 'nn0red', 'n e. RR')
    le16 = S([nu, w.inst('eluzle')], 'syl', '; 1 6 <_ n')
    nlt = S([le16, S([S([num.re_nat(w, 16)], 'a1i', '; 1 6 e. RR'), nr, w.inst('lenlt')], 'syl2anc', '( ; 1 6 <_ n <-> -. n < ; 1 6 )')], 'mpbid', '-. n < ; 1 6')
    FVn = subst_text(FBODY, {'x': 'n'})
    GETDn = subst_text(tx(GETD), {'x': 'n'})
    SR = '( ( ( C ScTM K ) ` n ) Search n )'
    X = '( 2nd ` ( 1st ` %s ) )' % SR
    fv, _ = fvm(w, ph, FM, None, 'x', 'NN0', FBODY, 'n', nn, S([w.s([], 'ifex', '%s e. _V' % FVn)], 'a1i', '%s e. _V' % FVn))
    f1 = S([fv, S([nlt], 'iffalsed', '%s = %s' % (FVn, GETDn))], 'eqtrd', '( %s ` n ) = %s' % (FM, GETDn))
    g1 = S([S([ne], 'neneqd', '-. ( 1st ` %s ) = ( inr ` (/) )' % SR)], 'iffalsed', '%s = %s' % (GETDn, X))
    fx = S([f1, g1], 'eqtrd', '( %s ` n ) = %s' % (FM, X))
    c1 = S([], 'simpll', '') if False else None
    cc = S([bs], 'simpld', '( C e. NN0 /\\ 1 <_ C )')
    kn = S([bs], 'simprd', 'K e. NN')
    SCn = '( ( C ScTM K ) ` n )'
    sc = S([cc, kn, nu, w.inst('sctm16')], 'syl3anc', '( %s e. Scales /\\ 1 <_ ( 1st ` ( 1st ` ( 1st ` %s ) ) ) )' % (SCn, SCn))
    gd = S([S([sc], 'simpld', '%s e. Scales' % SCn), nn, w.inst('srchgetd')], 'syl2anc', '%s e. ( NN0 X. Word NN0 )' % GETDn)
    xd = S([g1, gd], 'eqeltrrd', '%s e. ( NN0 X. Word NN0 )' % X)
    x2 = S([xd, w.inst('xp2nd')], 'syl', '( 2nd ` %s ) e. Word NN0' % X)
    fn = S([x2, w.inst('wrdfn')], 'syl', '( 2nd ` %s ) Fn ( 0 ..^ ( # ` ( 2nd ` %s ) ) )' % (X, X))
    Sx = '( 2nd ` %s )' % X
    RAN = 'A. b e. ran %s b e. Prime' % Sx
    RANI = 'A. i e. ( 0 ..^ ( # ` %s ) ) ( %s ` i ) e. Prime' % (Sx, Sx)
    rq = w.s([], 'eleq1', '( b = ( %s ` i ) -> ( b e. Prime <-> ( %s ` i ) e. Prime ) )' % (Sx, Sx))
    rr = S([fn, w.s([rq], 'ralrn', '( %s Fn ( 0 ..^ ( # ` %s ) ) -> ( %s <-> %s ) )' % (Sx, Sx, RAN, RANI))], 'mpd' if False else 'syl', '') if False else None
    rr = w.s([fn, w.s([rq], 'ralrn', '( %s Fn ( 0 ..^ ( # ` %s ) ) -> ( %s <-> %s ) )' % (Sx, Sx, RAN, RANI))], 'syl', '( %s -> ( %s <-> %s ) )' % (ph, RAN, RANI))
    leaves = {}

    def walk(txt, st):
        parts = and_parts(txt)
        if parts is None:
            leaves[txt] = st; return
        refs = ['simpld', 'simprd'] if len(parts) == 2 else ['simp1d', 'simp2d', 'simp3d']
        for p_, r_ in zip(parts, refs):
            walk(p_, S([st], r_, p_))
    walk(sp[1], p2)
    assert RAN in leaves
    leaves[RANI] = S([leaves[RAN], rr], 'mpbid', RANI)
    PX = PROPSf.replace('( f ` n )', X)
    px = build_conj(w, ph, PX, leaves)
    PF = subst_text(PROPSf, {'f': FM}) if False else PROPSf.replace('( f ` n )', '( %s ` n )' % FM)
    # congruence ( FM ` n ) -> X under the equality alone
    ante = '( %s ` n ) = %s' % (FM, X)
    idq = w.s([], 'id', '( %s -> %s )' % (ante, ante))
    eqs, new = w.wcongr(PF, {}, ante, {}, rules={'( %s ` n )' % FM: (X, idq)})
    assert new == PX, (new[:200], PX[:200])
    bi = w.s([fx, eqs], 'syl', '( %s -> ( %s <-> %s ) )' % (ph, PF, PX))
    w.qed([px, bi], 'mpbird', '( %s -> %s )' % (ph, PF))
    return w


GENS['t15corr'] = t15corr



def SBx(e, n):
    return subst_text(SUCCB, {'e': e, 'n': n})


SUCCP = 'A. y e. RR ( 0 < y -> E. t e. NN0 A. z e. ( ZZ>= ` t ) %s )' % SBx('y', 'z')
CORRF = CORRC.replace('( f ` n )', '( %s ` n )' % FM)


def t15corrall():
    w = W('t15corrall', 'The correctness clause of carmtm for the output function f of the concrete machine, from the success clause of the algorithm (bound letters renamed).')
    base = '( ( C e. NN0 /\\ 1 <_ C ) /\\ K e. NN )'
    ph = '( %s /\\ %s )' % (base, SUCCP)
    pe = '( %s /\\ e e. RR+ )' % ph
    E = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (pe, f))
    em = E([], 'simpr', 'e e. RR+')
    er = E([em, w.inst('rpre')], 'syl', 'e e. RR')
    ep = E([em, w.inst('rpgt0')], 'syl', '0 < e')
    sp = E([], 'simplr', SUCCP)
    body = '( 0 < y -> E. t e. NN0 A. z e. ( ZZ>= ` t ) %s )' % SBx('y', 'z')
    eq = 'y = e'
    idq = w.s([], 'id', '( %s -> %s )' % (eq, eq))
    cq, newb = w.wcongr(body, {'y': 'e'}, eq, {'y': idq})
    rs = w.s([cq], 'rspcv', '( e e. RR -> ( %s -> %s ) )' % (SUCCP, newb))
    r1 = E([er, sp, rs], 'sylc', newb)
    r2 = E([ep, r1], 'mpd', 'E. t e. NN0 A. z e. ( ZZ>= ` t ) %s' % SBx('e', 'z'))
    # rename
    eqz = 'z = n'
    idz = w.s([], 'id', '( %s -> %s )' % (eqz, eqz))
    cz, nz = w.wcongr(SBx('e', 'z'), {'z': 'n'}, eqz, {'z': idz})
    rv = w.s([cz], 'cbvralvw', '( A. z e. ( ZZ>= ` t ) %s <-> A. n e. ( ZZ>= ` t ) %s )' % (SBx('e', 'z'), SBx('e', 'n')))
    rb = w.s([rv], 'rexbii', '( E. t e. NN0 A. z e. ( ZZ>= ` t ) %s <-> E. t e. NN0 A. n e. ( ZZ>= ` t ) %s )' % (SBx('e', 'z'), SBx('e', 'n')))
    ct = w.s([w.s([w.s([], 'id', '( t = m -> t = m )')], 'fveq2d', '( t = m -> ( ZZ>= ` t ) = ( ZZ>= ` m ) )')], 'raleqdv',
             '( t = m -> ( A. n e. ( ZZ>= ` t ) %s <-> A. n e. ( ZZ>= ` m ) %s ) )' % (SBx('e', 'n'), SBx('e', 'n')))
    rt = w.s([ct], 'cbvrexvw', '( E. t e. NN0 A. n e. ( ZZ>= ` t ) %s <-> E. m e. NN0 A. n e. ( ZZ>= ` m ) %s )' % (SBx('e', 'n'), SBx('e', 'n')))
    r3 = E([r2, E([w.s([rb, rt], 'bitri', '( E. t e. NN0 A. z e. ( ZZ>= ` t ) %s <-> E. m e. NN0 A. n e. ( ZZ>= ` m ) %s )' % (SBx('e', 'z'), SBx('e', 'n')))], 'a1i',
                                   '( E. t e. NN0 A. z e. ( ZZ>= ` t ) %s <-> E. m e. NN0 A. n e. ( ZZ>= ` m ) %s )' % (SBx('e', 'z'), SBx('e', 'n')))], 'mpbid',
           'E. m e. NN0 A. n e. ( ZZ>= ` m ) %s' % SBx('e', 'n'))
    s1 = w.s([], 'id', '( n e. ( ZZ>= ` ; 1 6 ) -> n e. ( ZZ>= ` ; 1 6 ) )')
    s2 = w.s([s1], 'rgen', 'A. n e. ( ZZ>= ` ; 1 6 ) n e. ( ZZ>= ` ; 1 6 )')
    c1 = w.s([w.s([w.s([], 'id', '( m = ; 1 6 -> m = ; 1 6 )')], 'fveq2d', '( m = ; 1 6 -> ( ZZ>= ` m ) = ( ZZ>= ` ; 1 6 ) )')], 'raleqdv',
             '( m = ; 1 6 -> ( A. n e. ( ZZ>= ` m ) n e. ( ZZ>= ` ; 1 6 ) <-> A. n e. ( ZZ>= ` ; 1 6 ) n e. ( ZZ>= ` ; 1 6 ) ) )')
    e3 = w.s([num.nn0(w, 16), s2, w.s([c1], 'rspcev', '( ( ; 1 6 e. NN0 /\\ A. n e. ( ZZ>= ` ; 1 6 ) n e. ( ZZ>= ` ; 1 6 ) ) -> E. m e. NN0 A. n e. ( ZZ>= ` m ) n e. ( ZZ>= ` ; 1 6 ) )')], 'mp2an',
             'E. m e. NN0 A. n e. ( ZZ>= ` m ) n e. ( ZZ>= ` ; 1 6 )')
    PSI = '( %s /\\ n e. ( ZZ>= ` ; 1 6 ) )' % SBx('e', 'n')
    r4 = E([r3, E([e3], 'a1i', 'E. m e. NN0 A. n e. ( ZZ>= ` m ) n e. ( ZZ>= ` ; 1 6 )'), w.inst('extrwevan')], 'syl2anc', 'E. m e. NN0 A. n e. ( ZZ>= ` m ) %s' % PSI)
    PR = PROPSf.replace('( f ` n )', '( %s ` n )' % FM)
    pn = '( ( %s /\\ n e. NN0 ) /\\ %s )' % (pe, PSI)
    N = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (pn, f))
    bs = N([], 'simplll' if False else 'simplll', '') if False else None
    bs = N([w.s([], 'simpll', '( %s -> %s )' % (pe, ph)) if False else w.s([], 'simpll', '( %s -> %s )' % (pe, base))], 'ad2antrr' if False else 'id', '') if False else None
    bs0 = w.s([], 'simpll', '( %s -> %s )' % (pe, base))
    bsn = w.s([bs0], 'ad2antrr', '( %s -> %s )' % (pn, base))
    ps = N([], 'simpr', PSI)
    cr = N([N([bsn, N([ps], 'simprd', 'n e. ( ZZ>= ` ; 1 6 )')], 'jca', '( %s /\\ n e. ( ZZ>= ` ; 1 6 ) )' % base), N([ps], 'simpld', SBx('e', 'n'))], 'jca',
           '( ( %s /\\ n e. ( ZZ>= ` ; 1 6 ) ) /\\ %s )' % (base, SBx('e', 'n')))
    one = N([cr, w.inst('t15corr')], 'syl', PR)
    im = w.s([one], 'ex', '( ( %s /\\ n e. NN0 ) -> ( %s -> %s ) )' % (pe, PSI, PR))
    al = E([im], 'ralrimiva', 'A. n e. NN0 ( %s -> %s )' % (PSI, PR))
    ev = E([r4, al, w.inst('extrwevim')], 'syl2anc', 'E. m e. NN0 A. n e. ( ZZ>= ` m ) %s' % PR)
    w.qed([ev], 'ralrimiva', '( %s -> %s )' % (ph, CORRF))
    return w


GENS['t15corrall'] = t15corrall



def carmtmw():
    w = W('carmtmw', 'The main theorem of carmichael.tex in the machine model, conditional on the AGP 3.1 pigeonhole statement (the hypotheses of ~ carmsw ): a TM2 machine computes, from n, a Carmichael number in ( n , n ^ ( 1 + e ) ] with its prime factorization, in time exp ( c log n log log n ) (milestone M-W).')
    txt = open(os.path.join(ROOT, 'carmichael.mm')).read()
    hy = []
    for m in re.finditer(r'carmswn\.(\d) \$e \|- (.*?) \$\.', txt, re.S):
        f = ' '.join(m.group(2).split())
        w.lines.append('h%s::carmtmw.%s |- %s' % (m.group(1), m.group(1), f))
        hy.append('h%s' % m.group(1))
    G = GTXT
    cs = w.s(hy, 'carmswn', '( ph -> E. c e. NN0 E. k e. NN %s )' % BODYW)
    Buk = subst_text(BODYW, {'c': 'u'})
    Buv = subst_text(Buk, {'k': 'v'})
    q1 = w.s([], 'id', '( c = u -> c = u )')
    b1, n1 = w.wcongr(BODYW, {'c': 'u'}, 'c = u', {'c': q1})
    assert n1 == Buk
    q2 = w.s([], 'id', '( k = v -> k = v )')
    b2, n2 = w.wcongr(Buk, {'k': 'v'}, 'k = v', {'k': q2})
    assert n2 == Buv
    cb = w.s([b1, b2], 'cbvrex2vw', '( E. c e. NN0 E. k e. NN %s <-> E. u e. NN0 E. v e. NN %s )' % (BODYW, Buv))
    cs2 = w.s([cs, cb], 'sylib', '( ph -> E. u e. NN0 E. v e. NN %s )' % Buv)
    # inside
    pu = '( ( ph /\\ ( u e. NN0 /\\ v e. NN ) ) /\\ %s )' % Buv
    U = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (pu, f))
    uv = U([], 'simplr', '( u e. NN0 /\\ v e. NN )')
    un = U([uv], 'simpld', 'u e. NN0'); vn = U([uv], 'simprd', 'v e. NN')
    bd = U([], 'simpr', Buv)
    bp = and_parts(Buv)
    cv = U([bd], 'simpld', bp[0]); cs_ = U([bd], 'simprd', bp[1])
    u1000 = U([cv], 'simpld', and_parts(bp[0])[0])
    ur = U([un], 'nn0red', 'u e. RR')
    u1 = linarith(w, pu, [u1000], '1 <_ u', leaves={'u': ur})
    cp = and_parts(bp[1])
    cost = U([cs_], 'simpld', cp[0]); succ = U([cs_], 'simprd', cp[1])
    b1000 = U([U([un, u1000], 'jca', '( u e. NN0 /\\ ; ; ; 1 0 0 0 <_ u )'), vn], 'jca', '( ( u e. NN0 /\\ ; ; ; 1 0 0 0 <_ u ) /\\ v e. NN )')
    base1 = U([U([un, u1], 'jca', '( u e. NN0 /\\ 1 <_ u )'), vn], 'jca', '( ( u e. NN0 /\\ 1 <_ u ) /\\ v e. NN )')
    m_uv = {'C': 'u', 'K': 'v'}
    GMuv = subst_text(GM, m_uv); FMuv = subst_text(FM, m_uv)
    CHIuv = subst_text(CHI, m_uv)
    gv = U([U([b1000, cost], 'jca', '( ( ( u e. NN0 /\\ ; ; ; 1 0 0 0 <_ u ) /\\ v e. NN ) /\\ %s )' % cp[0]), w.inst('t15gev')], 'syl',
           'E. m e. NN0 A. n e. ( ZZ>= ` m ) %s' % CHIuv)
    cz = w.s([w.s([w.s([], 'id', '( m = z -> m = z )')], 'fveq2d', '( m = z -> ( ZZ>= ` m ) = ( ZZ>= ` z ) )')], 'raleqdv',
             '( m = z -> ( A. n e. ( ZZ>= ` m ) %s <-> A. n e. ( ZZ>= ` z ) %s ) )' % (CHIuv, CHIuv))
    rz = w.s([cz], 'cbvrexvw', '( E. m e. NN0 A. n e. ( ZZ>= ` m ) %s <-> E. z e. NN0 A. n e. ( ZZ>= ` z ) %s )' % (CHIuv, CHIuv))
    gv2 = U([gv, U([rz], 'a1i', '( E. m e. NN0 A. n e. ( ZZ>= ` m ) %s <-> E. z e. NN0 A. n e. ( ZZ>= ` z ) %s )' % (CHIuv, CHIuv))], 'mpbid',
            'E. z e. NN0 A. n e. ( ZZ>= ` z ) %s' % CHIuv)
    # SUCC -> SUCCP
    SUCCuv = cp[1]
    SBy = lambda e, n: subst_text(SBx(e, n), m_uv)
    SUCCPuv = subst_text(SUCCP, m_uv)
    qa = w.s([], 'id', '( n = z -> n = z )')
    ca, na = w.wcongr(SBy('y', 'n'), {'n': 'z'}, 'n = z', {'n': qa})
    ra = w.s([ca], 'cbvralvw', '( A. n e. ( ZZ>= ` m ) %s <-> A. z e. ( ZZ>= ` m ) %s )' % (SBy('y', 'n'), SBy('y', 'z')))
    rb_ = w.s([ra], 'rexbii', '( E. m e. NN0 A. n e. ( ZZ>= ` m ) %s <-> E. m e. NN0 A. z e. ( ZZ>= ` m ) %s )' % (SBy('y', 'n'), SBy('y', 'z')))
    ct = w.s([w.s([w.s([], 'id', '( m = t -> m = t )')], 'fveq2d', '( m = t -> ( ZZ>= ` m ) = ( ZZ>= ` t ) )')], 'raleqdv',
             '( m = t -> ( A. z e. ( ZZ>= ` m ) %s <-> A. z e. ( ZZ>= ` t ) %s ) )' % (SBy('y', 'z'), SBy('y', 'z')))
    rc = w.s([ct], 'cbvrexvw', '( E. m e. NN0 A. z e. ( ZZ>= ` m ) %s <-> E. t e. NN0 A. z e. ( ZZ>= ` t ) %s )' % (SBy('y', 'z'), SBy('y', 'z')))
    rd = w.s([rb_, rc], 'bitri', '( E. m e. NN0 A. n e. ( ZZ>= ` m ) %s <-> E. t e. NN0 A. z e. ( ZZ>= ` t ) %s )' % (SBy('y', 'n'), SBy('y', 'z')))
    re_ = w.s([rd], 'imbi2i', '( ( 0 < y -> E. m e. NN0 A. n e. ( ZZ>= ` m ) %s ) <-> ( 0 < y -> E. t e. NN0 A. z e. ( ZZ>= ` t ) %s ) )' % (SBy('y', 'n'), SBy('y', 'z')))
    rf = w.s([re_], 'ralbii', '( A. y e. RR ( 0 < y -> E. m e. NN0 A. n e. ( ZZ>= ` m ) %s ) <-> %s )' % (SBy('y', 'n'), SUCCPuv))
    qe = w.s([], 'id', '( e = y -> e = y )')
    inner = '( 0 < e -> E. m e. NN0 A. n e. ( ZZ>= ` m ) %s )' % SBy('e', 'n')
    ce, ne_ = w.wcongr(inner, {'e': 'y'}, 'e = y', {'e': qe})
    rg = w.s([ce], 'cbvralvw', '( %s <-> A. y e. RR %s )' % (SUCCuv, ne_))
    rh = w.s([rg, rf], 'bitri', '( %s <-> %s )' % (SUCCuv, SUCCPuv))
    sp = U([succ, U([rh], 'a1i', '( %s <-> %s )' % (SUCCuv, SUCCPuv))], 'mpbid', SUCCPuv)
    corr = U([U([base1, sp], 'jca', '( ( ( u e. NN0 /\\ 1 <_ u ) /\\ v e. NN ) /\\ %s )' % SUCCPuv), w.inst('t15corrall')], 'syl', subst_text(CORRF, m_uv))
    gty = U([base1, w.inst('t15gty')], 'syl', '%s : NN0 --> NN0' % GMuv)
    fty = U([base1, w.inst('t15fty')], 'syl', '%s : NN0 --> ( NN0 X. Word NN0 )' % FMuv)
    # the time function
    pz = '( ( %s /\\ z e. NN0 ) /\\ A. n e. ( ZZ>= ` z ) %s )' % (pu, CHIuv)
    Z_ = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (pz, f))
    subz = lambda st, f: w.s([st], 'ad2antrr', '( %s -> %s )' % (pz, f))
    zn = Z_([], 'simplr', 'z e. NN0')
    ch = Z_([], 'simpr', 'A. n e. ( ZZ>= ` z ) %s' % CHIuv)
    A_, B_ = split_imp(stmt_of('tmfun'))
    mt = {'G': GMuv, 'C': '; ; ; 2 0 0 1', 'M': 'z'}
    A2, B2 = subst_text(A_, mt), subst_text(B_, mt)
    r2001 = Z_([w.s([w.s([num.nn(w, 2001)], 'nnrpi', '; ; ; 2 0 0 1 e. RR+')], 'id', '') if False else w.s([num.nn(w, 2001), w.inst('nnrp')], 'ax-mp', '; ; ; 2 0 0 1 e. RR+')], 'a1i', '; ; ; 2 0 0 1 e. RR+')
    L = {'%s : NN0 --> NN0' % GMuv: subz(gty, '%s : NN0 --> NN0' % GMuv), '; ; ; 2 0 0 1 e. RR+': r2001, 'z e. NN0': zn,
         'A. n e. ( ZZ>= ` z ) %s' % CHIuv: ch}
    tf, ftf = use(w, pz, 'tmfun', mt, L)
    tp = and_parts(B2)
    TFc = tp[0][:-len(' : NN0 --> NN0')]
    t1 = Z_([tf], 'simp1d', tp[0]); t2 = Z_([tf], 'simp2d', tp[1]); t3 = Z_([tf], 'simp3d', tp[2])
    b1z = subz(base1, '( ( u e. NN0 /\\ 1 <_ u ) /\\ v e. NN )')
    HH = '( %s : NN0 --> NN0 /\\ %s )' % (TFc, tp[1])
    comp = Z_([Z_([b1z, Z_([t1, t2], 'jca', HH)], 'jca', '( ( ( u e. NN0 /\\ 1 <_ u ) /\\ v e. NN ) /\\ %s )' % HH), w.inst('t15comp')], 'syl',
              subst_text('%s TM2CompT %s' % (HT, ENCT), dict(m_uv, H=TFc)))
    HTc = subst_text(HT, dict(m_uv, H=TFc))
    ENCTc = subst_text(ENCT, m_uv)
    # time: ( 2nd ` ( 2nd ` HTc ) ) = TFc
    MAc = '( TMMach u v )'
    IP = "<. <. ( _I |` Gamma' ) , ( _I |` Gamma' ) >. , %s >." % TFc
    mx = w.s([w.s([], 'df-tmmach', stmt_of('df-tmmach').replace('( TMMach C K )', MAc).replace('( TMTy C K )', '( TMTy u v )').replace('( TMProg C K )', '( TMProg u v )')) if False else None], 'id', '') if False else None
    mdf = subst_text(stmt_of('df-tmmach'), {'C': 'u', 'K': 'v'})
    mrhs = mdf.split(' = ', 1)[1]
    mxs = w.s([w.s([], 'df-tmmach', mdf), w.s([], 'opex', '%s e. _V' % mrhs)], 'eqeltri', '%s e. _V' % MAc)
    tfx = w.s([w.s([], 'nn0ex', 'NN0 e. _V')], 'mptex', '%s e. _V' % TFc)
    o1 = w.s([mxs, w.s([], 'opex', '%s e. _V' % IP), w.inst('op2ndg')], 'mp2an', '( 2nd ` %s ) = %s' % (HTc, IP))
    o2 = w.s([w.s([], 'opex', "<. ( _I |` Gamma' ) , ( _I |` Gamma' ) >. e. _V"), tfx, w.inst('op2ndg')], 'mp2an', '( 2nd ` %s ) = %s' % (IP, TFc))
    o3 = w.s([w.s([o1], 'fveq2i', '( 2nd ` ( 2nd ` %s ) ) = ( 2nd ` %s )' % (HTc, IP)), o2], 'eqtri', '( 2nd ` ( 2nd ` %s ) ) = %s' % (HTc, TFc))
    TB = lambda F_: '( ( %s ` n ) <_ ( exp ` ( ( ; ; ; 2 0 0 1 x. ( log ` n ) ) x. ( log ` ( log ` n ) ) ) ) )' % F_
    o4 = w.s([w.s([o3], 'fveq1i', '( ( 2nd ` ( 2nd ` %s ) ) ` n ) = ( %s ` n )' % (HTc, TFc))], 'breq1i',
             '( ( ( 2nd ` ( 2nd ` %s ) ) ` n ) <_ ( exp ` ( ( ; ; ; 2 0 0 1 x. ( log ` n ) ) x. ( log ` ( log ` n ) ) ) ) <-> ( %s ` n ) <_ ( exp ` ( ( ; ; ; 2 0 0 1 x. ( log ` n ) ) x. ( log ` ( log ` n ) ) ) ) )' % (HTc, TFc))
    o5 = w.s([o4], 'ralbii', '( A. n e. ( ZZ>= ` ( z + 3 ) ) ( ( 2nd ` ( 2nd ` %s ) ) ` n ) <_ ( exp ` ( ( ; ; ; 2 0 0 1 x. ( log ` n ) ) x. ( log ` ( log ` n ) ) ) ) <-> %s )' % (HTc, tp[2]))
    t3b = Z_([t3, Z_([o5], 'a1i', '( A. n e. ( ZZ>= ` ( z + 3 ) ) ( ( 2nd ` ( 2nd ` %s ) ) ` n ) <_ ( exp ` ( ( ; ; ; 2 0 0 1 x. ( log ` n ) ) x. ( log ` ( log ` n ) ) ) ) <-> %s )' % (HTc, tp[2]))], 'mpbird',
             'A. n e. ( ZZ>= ` ( z + 3 ) ) ( ( 2nd ` ( 2nd ` %s ) ) ` n ) <_ ( exp ` ( ( ; ; ; 2 0 0 1 x. ( log ` n ) ) x. ( log ` ( log ` n ) ) ) )' % HTc)
    TIMEh = TIMEC.replace('( 2nd ` ( 2nd ` h ) )', '( 2nd ` ( 2nd ` %s ) )' % HTc)
    ps0 = TIMEh[len('E. c e. RR+ E. m e. NN0 '):]
    qc = w.s([], 'id', '( c = ; ; ; 2 0 0 1 -> c = ; ; ; 2 0 0 1 )')
    cc1, pc1 = w.wcongr(ps0, {'c': '; ; ; 2 0 0 1'}, 'c = ; ; ; 2 0 0 1', {'c': qc})
    qm = w.s([], 'id', '( m = ( z + 3 ) -> m = ( z + 3 ) )')
    cc2, pc2 = w.wcongr(pc1, {'m': '( z + 3 )'}, 'm = ( z + 3 )', {'m': qm})
    z3 = Z_([zn, Z_([w.s([], '3nn0', '3 e. NN0')], 'a1i', '3 e. NN0')], 'nn0addcld', '( z + 3 ) e. NN0')
    re2 = w.s([cc1, cc2], 'rspc2ev', '( ( ; ; ; 2 0 0 1 e. RR+ /\\ ( z + 3 ) e. NN0 /\\ %s ) -> %s )' % (pc2, TIMEh))
    assert pc2 == 'A. n e. ( ZZ>= ` ( z + 3 ) ) ( ( 2nd ` ( 2nd ` %s ) ) ` n ) <_ ( exp ` ( ( ; ; ; 2 0 0 1 x. ( log ` n ) ) x. ( log ` ( log ` n ) ) ) )' % HTc, pc2[:150]
    tim = Z_([r2001, z3, t3b, re2], 'syl3anc', TIMEh)
    CORRc = subst_text(CORRF, m_uv)
    corrz = subz(corr, CORRc)
    inner_h = '( %s TM2CompT %s /\\ ( %s /\\ %s ) )' % (HTc, ENCTc, TIMEh, CORRc)
    ih = Z_([comp, Z_([tim, corrz], 'jca', '( %s /\\ %s )' % (TIMEh, CORRc))], 'jca', inner_h)
    # E. h
    PSIH = '( h TM2CompT %s /\\ ( %s /\\ %s ) )' % (ENCTc, TIMEC, CORRc)
    qh = w.s([], 'id', '( h = %s -> h = %s )' % (HTc, HTc))
    ch_, nh = w.wcongr(PSIH, {'h': HTc}, 'h = %s' % HTc, {'h': qh})
    assert nh == inner_h, (nh[:300], inner_h[:300])
    hx = Z_([w.s([], 'opex', '%s e. _V' % HTc)], 'a1i', '%s e. _V' % HTc)
    eh = Z_([hx, ih, ch_], 'spcedv', 'E. h %s' % PSIH)
    # E. f
    PSIF = G[len('E. f '):]
    PSIFc = PSIF.replace('f :', '%s :' % FMuv, 1) if False else None
    qf = w.s([], 'id', '( f = %s -> f = %s )' % (FMuv, FMuv))
    PSIHf = PSIF[len('( f : NN0 --> ( NN0 X. Word NN0 ) /\\ E. h '):-2]
    c2, n2_ = w.wcongr(PSIHf, {'f': FMuv}, 'f = %s' % FMuv, {'f': qf})
    assert n2_ == PSIH, (n2_[:300], PSIH[:300])
    c1 = w.s([], 'feq1', '( f = %s -> ( f : NN0 --> ( NN0 X. Word NN0 ) <-> %s : NN0 --> ( NN0 X. Word NN0 ) ) )' % (FMuv, FMuv))
    c3 = w.s([c2], 'exbidv', '( f = %s -> ( E. h %s <-> E. h %s ) )' % (FMuv, PSIHf, PSIH))
    got = '( %s : NN0 --> ( NN0 X. Word NN0 ) /\\ E. h %s )' % (FMuv, PSIH)
    cf = w.s([c1, c3], 'anbi12d', '( f = %s -> ( %s <-> %s ) )' % (FMuv, PSIF, got))
    fbody = Z_([subz(fty, '%s : NN0 --> ( NN0 X. Word NN0 )' % FMuv), eh], 'jca', got)
    fx = Z_([w.s([w.s([], 'nn0ex', 'NN0 e. _V')], 'mptex', '%s e. _V' % FMuv)], 'a1i', '%s e. _V' % FMuv)
    gz = Z_([fx, fbody, cf], 'spcedv', G)
    # eliminate z, u, v
    gz2 = w.s([gz], 'ex', '( ( %s /\\ z e. NN0 ) -> ( A. n e. ( ZZ>= ` z ) %s -> %s ) )' % (pu, CHIuv, G))
    gz3 = w.s([gz2], 'rexlimdva', '( %s -> ( E. z e. NN0 A. n e. ( ZZ>= ` z ) %s -> %s ) )' % (pu, CHIuv, G))
    gu = w.s([gv2, gz3], 'mpd', '( %s -> %s )' % (pu, G))
    gu2 = w.s([gu], 'exp31', '( ph -> ( ( u e. NN0 /\\ v e. NN ) -> ( %s -> %s ) ) )' % (Buv, G))
    gu3 = w.s([gu2], 'rexlimdvv', '( ph -> ( E. u e. NN0 E. v e. NN %s -> %s ) )' % (Buv, G))
    w.qed([cs2, gu3], 'mpd', '( ph -> %s )' % G)
    return w


GENS['carmtmw'] = carmtmw

if __name__ == '__main__':
    for lab in sys.argv[1:]:
        GENS[lab]().run()
