"""Sortie ZBV2, section 3 part C: the local factors g(p), (d/phi d)^2 as a divisor sum,
and W_bound (ZBV2-blueprint.md section 3.2).
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from zbv2lib import *
import num
from zbv2_phisg import prfacts, cxpfacts
from zbv2_useq import ufacts

PG = lambda d: 'prod_ p e. %s %s' % (PRF(d), GS('p'))
RAT2 = lambda n: '( ( %s / ( phi ` %s ) ) ^ 2 )' % (n, n)
PM1 = '( p - 1 )'


def gsfacts(w, ante, pf):
    """under ante with prfacts pf: GS(p) e. RR, 0 <_ GS(p), CC; ( p - 1 ) e. RR, CC, =/= 0"""
    st = mkst(w, ante)
    one = st([], '1red', '1 e. RR')
    nume = st([st([w.s([num.re_nat(w, 2)], 'a1i', '( %s -> 2 e. RR )' % ante), pf['re']], 'remulcld', '( 2 x. p ) e. RR'), one], 'resubcld', '( ( 2 x. p ) - 1 ) e. RR')
    num0 = linarith(w, ante, [pf['ge2']], '0 <_ ( ( 2 x. p ) - 1 )', leaves={'p': pf['re']})
    m1re = st([pf['re'], one], 'resubcld', '%s e. RR' % PM1)
    m1gt = linarith(w, ante, [pf['ge2']], '0 < %s' % PM1, leaves={'p': pf['re']})
    m1ne = st([m1gt], 'gt0ne0d', '%s =/= 0' % PM1)
    sqgt = st([m1re, m1ne], 'sqgt0d', '0 < ( %s ^ 2 )' % PM1)
    sqre = st([m1re, w.s([w.s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % ante)], 'reexpcld', '( %s ^ 2 ) e. RR' % PM1)
    sqrp = st([sqre, sqgt], 'elrpd', '( %s ^ 2 ) e. RR+' % PM1)
    gre = st([nume, sqrp], 'rerpdivcld', '%s e. RR' % GS('p'))
    g0 = st([nume, sqrp, num0], 'divge0d', '0 <_ %s' % GS('p'))
    return dict(nume=nume, num0=num0, m1re=m1re, m1ne=m1ne, m1cc=st([m1re], 'recnd', '%s e. CC' % PM1), sqrp=sqrp,
                gre=gre, g0=g0, gcc=st([gre], 'recnd', '%s e. CC' % GS('p')))


def pgfacts(w, ante, dnn, d):
    """PG(d) e. RR, 0 <_ PG(d), IFF(d) e. RR, 0 <_ IFF(d)"""
    st = mkst(w, ante)
    AP = '( %s /\\ p e. %s )' % (ante, PRF(d)); sp = mkst(w, AP)
    pf = prfacts(w, AP, sp([], 'simpr', 'p e. %s' % PRF(d)), d)
    g = gsfacts(w, AP, pf)
    fin = sy(w, ante, dnn, 'pffinq', '%s e. Fin' % PRF(d))
    pre = st([fin, g['gre']], 'fprodrecl', '%s e. RR' % PG(d))
    p0 = st([w.s([], 'nfv', 'F/ p %s' % ante), fin, g['gre'], g['g0']], 'fprodge0', '0 <_ %s' % PG(d))
    drp = st([dnn], 'nnrpd', '%s e. RR+' % d)
    Q = '( %s / %s )' % (PG(d), d)
    qre = st([pre, drp], 'rerpdivcld', '%s e. RR' % Q)
    q0 = st([pre, drp, p0], 'divge0d', '0 <_ %s' % Q)
    C = '( mmu ` %s ) =/= 0' % d
    AT = '( %s /\\ %s )' % (ante, C); AF = '( %s /\\ -. %s )' % (ante, C)
    ifre = st([lift(w, qre, AT), w.s([], '0red', '( %s -> 0 e. RR )' % AF)], 'ifclda', '%s e. RR' % IFF(d))
    b1 = w.s([], 'breq2', '( %s = %s -> ( 0 <_ %s <-> 0 <_ %s ) )' % (Q, IFF(d), Q, IFF(d)))
    b2 = w.s([], 'breq2', '( 0 = %s -> ( 0 <_ 0 <-> 0 <_ %s ) )' % (IFF(d), IFF(d)))
    if0 = w.s([b1, b2, lift(w, q0, AT), w.s([w.s([], '0le0', '0 <_ 0')], 'a1i', '( %s -> 0 <_ 0 )' % AF)], 'ifbothda', '( %s -> 0 <_ %s )' % (ante, IFF(d)))
    return dict(pre=pre, p0=p0, fin=fin, qre=qre, q0=q0, ifre=ifre, if0=if0, ifcc=st([ifre], 'recnd', '%s e. CC' % IFF(d)))


def igfacts(w, ante, bnn, b):
    """IFG(b) e. RR, 0 <_ IFG(b), IFG(b) <_ ( 1 / b )"""
    st = mkst(w, ante)
    brp = st([bnn], 'nnrpd', '%s e. RR+' % b)
    R = '( 1 / %s )' % b
    rre = st([brp], 'rpreccld', '%s e. RR+' % R)
    rr = st([rre], 'rpred', '%s e. RR' % R)
    C = '( mmu ` %s ) =/= 0' % b
    AT = '( %s /\\ %s )' % (ante, C); AF = '( %s /\\ -. %s )' % (ante, C)
    ifre = st([lift(w, rr, AT), w.s([], '0red', '( %s -> 0 e. RR )' % AF)], 'ifclda', '%s e. RR' % IFG(b))
    b1 = w.s([], 'breq2', '( %s = %s -> ( 0 <_ %s <-> 0 <_ %s ) )' % (R, IFG(b), R, IFG(b)))
    b2 = w.s([], 'breq2', '( 0 = %s -> ( 0 <_ 0 <-> 0 <_ %s ) )' % (IFG(b), IFG(b)))
    if0 = w.s([b1, b2, lift(w, st([rre], 'rpge0d', '0 <_ %s' % R), AT), w.s([w.s([], '0le0', '0 <_ 0')], 'a1i', '( %s -> 0 <_ 0 )' % AF)], 'ifbothda',
              '( %s -> 0 <_ %s )' % (ante, IFG(b)))
    c1 = w.s([], 'breq1', '( %s = %s -> ( %s <_ %s <-> %s <_ %s ) )' % (R, IFG(b), R, R, IFG(b), R))
    c2 = w.s([], 'breq1', '( 0 = %s -> ( 0 <_ %s <-> %s <_ %s ) )' % (IFG(b), R, IFG(b), R))
    ifle = w.s([c1, c2, lift(w, st([rr], 'leidd', '%s <_ %s' % (R, R)), AT), lift(w, st([rre], 'rpge0d', '0 <_ %s' % R), AF)], 'ifbothda',
               '( %s -> %s <_ %s )' % (ante, IFG(b), R))
    return dict(rr=rr, ifre=ifre, if0=if0, ifle=ifle, ifcc=st([ifre], 'recnd', '%s e. CC' % IFG(b)))


def bvsqtot():
    w = W('bvsqtot', '( N / phi N )^2 is the divisor sum of prod_ p || d g(p) for squarefree N (Lean sq_div_totient_eq_sum; '
                     'sqfdvdsum at g, phirad).')
    A = SQF('N')
    st = mkst(w, A)
    nnn = st([], 'simpl', 'N e. NN'); sq = st([], 'simpr', A.split(' /\\ ')[1][:-2])
    G = '( t e. Prime |-> %s )' % GS('t')
    AT = '( %s /\\ t e. Prime )' % A; stt = mkst(w, AT)
    tp = stt([], 'simpr', 't e. Prime')
    # closure of GS(t) through prfacts-like facts for t
    tnn = sy(w, AT, tp, 'prmnn', 't e. NN'); tre = stt([tnn], 'nnred', 't e. RR')
    t2 = sy(w, AT, sy(w, AT, tp, 'prmuz2', 't e. ( ZZ>= ` 2 )'), 'eluzle', '2 <_ t')
    pft = dict(re=tre, ge2=t2)
    gt = gsfacts(w, AT, pft) if False else None
    one = stt([], '1red', '1 e. RR')
    nume = stt([stt([w.s([num.re_nat(w, 2)], 'a1i', '( %s -> 2 e. RR )' % AT), tre], 'remulcld', '( 2 x. t ) e. RR'), one], 'resubcld', '( ( 2 x. t ) - 1 ) e. RR')
    m1re = stt([tre, one], 'resubcld', '( t - 1 ) e. RR')
    m1ne = stt([linarith(w, AT, [t2], '0 < ( t - 1 )', leaves={'t': tre})], 'gt0ne0d', '( t - 1 ) =/= 0')
    sqre = stt([m1re, w.s([w.s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % AT)], 'reexpcld', '( ( t - 1 ) ^ 2 ) e. RR')
    sqne = stt([stt([m1re, m1ne], 'sqgt0d', '0 < ( ( t - 1 ) ^ 2 )')], 'gt0ne0d', '( ( t - 1 ) ^ 2 ) =/= 0')
    gtc = stt([stt([nume, sqre, sqne], 'redivcld', '%s e. RR' % GS('t'))], 'recnd', '%s e. CC' % GS('t'))
    gf = st([gtc], 'fmpttd', '%s : Prime --> CC' % G)
    sd = st([nnn, gf, w.inst('sqfdvdsum')], 'syl2anc', 'sum_ d e. %s prod_ p e. %s ( %s ` p ) = prod_ p e. %s ( 1 + ( %s ` p ) )' % (SQDV('N'), PRF('d'), G, PRF('N'), G))
    # values on the left
    AD = '( %s /\\ d e. %s )' % (A, SQDV('N')); sdd = mkst(w, AD)
    ADP = '( %s /\\ p e. %s )' % (AD, PRF('d')); sdp = mkst(w, ADP)
    pfd = prfacts(w, ADP, sdp([], 'simpr', 'p e. %s' % PRF('d')), 'd')
    vd, _ = mpv(w, ADP, 't', 'Prime', GS('t'), 'p', pfd['pp'], exs=w.s([], 'ovexd', '( %s -> %s e. _V )' % (ADP, GS('p'))))
    lhs = st([st([sdd([vd], 'prodeq2dv', 'prod_ p e. %s ( %s ` p ) = %s' % (PRF('d'), G, PG('d')))], 'sumeq2dv', 'sum_ d e. %s prod_ p e. %s ( %s ` p ) = sum_ d e. %s %s' % (SQDV('N'), PRF('d'), G, SQDV('N'), PG('d'))),
              st([sy(w, A, sq if False else st([nnn, st([], 'simpr', '( mmu ` N ) =/= 0')], 'jca', A), 'bvsqdv', '%s = %s' % (SQDV('N'), DV('N')))], 'sumeq1d', 'sum_ d e. %s %s = sum_ d e. %s %s' % (SQDV('N'), PG('d'), DV('N'), PG('d')))],
             'eqtrd', 'sum_ d e. %s prod_ p e. %s ( %s ` p ) = sum_ d e. %s %s' % (SQDV('N'), PRF('d'), G, DV('N'), PG('d')))
    # values on the right: 1 + g(p) = ( p / ( p - 1 ) ) x. ( p / ( p - 1 ) )
    AN = '( %s /\\ p e. %s )' % (A, PRF('N')); snp = mkst(w, AN)
    pfn = prfacts(w, AN, snp([], 'simpr', 'p e. %s' % PRF('N')), 'N')
    gn = gsfacts(w, AN, pfn)
    vn, _ = mpv(w, AN, 't', 'Prime', GS('t'), 'p', pfn['pp'], exs=w.s([], 'ovexd', '( %s -> %s e. _V )' % (AN, GS('p'))))
    Q = '( p / %s )' % PM1
    SQ = '( %s ^ 2 )' % PM1; SQM = '( %s x. %s )' % (PM1, PM1)
    NUMp = '( ( 2 x. p ) - 1 )'
    sqv = snp([gn['m1cc']], 'sqvald', '%s = %s' % (SQ, SQM))
    sqcc = snp([st([], 'id', '') if False else gn['sqrp']], 'rpcnd', '%s e. CC' % SQ)
    sqne = snp([gn['sqrp']], 'rpne0d', '%s =/= 0' % SQ)
    e_dd = snp([sqcc, snp([gn['nume']], 'recnd', '%s e. CC' % NUMp), sqcc, sqne], 'divdird', '( ( %s + %s ) / %s ) = ( ( %s / %s ) + ( %s / %s ) )' % (SQ, NUMp, SQ, SQ, SQ, NUMp, SQ))
    e_one = snp([e_dd, snp([snp([sqcc, sqne], 'dividd', '( %s / %s ) = 1' % (SQ, SQ))], 'oveq1d', '( ( %s / %s ) + %s ) = ( 1 + %s )' % (SQ, SQ, GS('p'), GS('p')))], 'eqtrd',
                '( ( %s + %s ) / %s ) = ( 1 + %s )' % (SQ, NUMp, SQ, GS('p')))
    # ( SQ + NUM ) = ( p ^ 2 )
    psq = snp([pfn['cc']], 'sqvald', '( p ^ 2 ) = ( p x. p )')
    lq = lineq(w, AN, '( %s + %s )' % (SQM, NUMp), '( p x. p )', leaves={'p': pfn['re']}, products=True)
    num2 = eqtr(w, AN, [snp([sqv], 'oveq1d', '( %s + %s ) = ( %s + %s )' % (SQ, NUMp, SQM, NUMp)), lq, snp([psq], 'eqcomd', '( p x. p ) = ( p ^ 2 )')], None)
    e_q = snp([pfn['cc'], gn['m1cc'], gn['m1ne']], 'sqdivd', '( %s ^ 2 ) = ( ( p ^ 2 ) / %s )' % (Q, SQ))
    one_g = eqtr(w, AN, [snp([e_one], 'eqcomd', '( 1 + %s ) = ( ( %s + %s ) / %s )' % (GS('p'), SQ, NUMp, SQ)),
                         snp([num2], 'oveq1d', '( ( %s + %s ) / %s ) = ( ( p ^ 2 ) / %s )' % (SQ, NUMp, SQ, SQ)),
                         snp([e_q], 'eqcomd', '( ( p ^ 2 ) / %s ) = ( %s ^ 2 )' % (SQ, Q))], None)
    qcc = snp([pfn['cc'], gn['m1cc'], gn['m1ne']], 'divcld', '%s e. CC' % Q)
    one_g2 = eqtr(w, AN, [snp([vn], 'oveq2d', '( 1 + ( %s ` p ) ) = ( 1 + %s )' % (G, GS('p'))), one_g, snp([qcc], 'sqvald', '( %s ^ 2 ) = ( %s x. %s )' % (Q, Q, Q))], None)
    PQ = 'prod_ p e. %s %s' % (PRF('N'), Q)
    fin = sy(w, A, nnn, 'pffinq', '%s e. Fin' % PRF('N'))
    fm = st([fin, qcc, qcc], 'fprodmul', 'prod_ p e. %s ( %s x. %s ) = ( %s x. %s )' % (PRF('N'), Q, Q, PQ, PQ))
    ph = sy(w, A, nnn, 'phirad', '( N / ( phi ` N ) ) = %s' % PQ)
    ratc = st([ph, st([fin, qcc], 'fprodcl', '%s e. CC' % PQ)], 'eqeltrd', '( N / ( phi ` N ) ) e. CC')
    rhs = eqtr(w, A, [st([one_g2], 'prodeq2dv', 'prod_ p e. %s ( 1 + ( %s ` p ) ) = prod_ p e. %s ( %s x. %s )' % (PRF('N'), G, PRF('N'), Q, Q)), fm,
                      st([st([ratc], 'sqvald', '%s = ( ( N / ( phi ` N ) ) x. ( N / ( phi ` N ) ) )' % RAT2('N')), st([ph, ph], 'oveq12d', '( ( N / ( phi ` N ) ) x. ( N / ( phi ` N ) ) ) = ( %s x. %s )' % (PQ, PQ))], 'eqtr2d',
                         '( %s x. %s ) = %s' % (PQ, PQ, RAT2('N')))], None)
    full = eqtr(w, A, [st([lhs], 'eqcomd', 'sum_ d e. %s %s = sum_ d e. %s prod_ p e. %s ( %s ` p )' % (DV('N'), PG('d'), SQDV('N'), PRF('d'), G)), sd, rhs], None)
    w.qed([full], 'eqcomd', STATEMENTS['bvsqtot'])
    return w


def bvgsu():
    w = W('bvgsu', 'prod_ p || A g(p) / A = prod_ p || A u(p) for squarefree A (the hsplit step of W_bound).')
    A = SQF('A')
    st = mkst(w, A)
    ann = st([], 'simpl', 'A e. NN')
    AP = '( %s /\\ p e. %s )' % (A, PRF('A')); sp = mkst(w, AP)
    pf = prfacts(w, AP, sp([], 'simpr', 'p e. %s' % PRF('A')), 'A')
    g = gsfacts(w, AP, pf)
    fin = sy(w, A, ann, 'pffinq', '%s e. Fin' % PRF('A'))
    PGA = PG('A'); PP = 'prod_ p e. %s p' % PRF('A')
    fd = st([fin, g['gcc'], pf['cc'], pf['ne']], 'fproddiv', 'prod_ p e. %s ( %s / p ) = ( %s / %s )' % (PRF('A'), GS('p'), PGA, PP))
    sid = w.s([], 'sqfprodid', '( %s -> %s = A )' % (A, PP))
    fd2 = st([fd, st([sid], 'oveq2d', '( %s / %s ) = ( %s / A )' % (PGA, PP, PGA))], 'eqtrd', 'prod_ p e. %s ( %s / p ) = ( %s / A )' % (PRF('A'), GS('p'), PGA))
    NUMp = '( ( 2 x. p ) - 1 )'; SQ = '( %s ^ 2 )' % PM1
    sqcc = sp([g['sqrp']], 'rpcnd', '%s e. CC' % SQ); sqne = sp([g['sqrp']], 'rpne0d', '%s =/= 0' % SQ)
    t1 = sp([sp([g['nume']], 'recnd', '%s e. CC' % NUMp), sqcc, pf['cc'], sqne, pf['ne']], 'divdiv1d', '( %s / p ) = ( %s / ( %s x. p ) )' % (GS('p'), NUMp, SQ))
    t2 = sp([sp([sqcc, pf['cc']], 'mulcomd', '( %s x. p ) = ( p x. %s )' % (SQ, SQ))], 'oveq2d', '( %s / ( %s x. p ) ) = %s' % (NUMp, SQ, U('p')))
    tt = sp([t1, t2], 'eqtrd', '( %s / p ) = %s' % (GS('p'), U('p')))
    pe = st([tt], 'prodeq2dv', 'prod_ p e. %s ( %s / p ) = prod_ p e. %s %s' % (PRF('A'), GS('p'), PRF('A'), U('p')))
    w.qed([fd2, pe], 'eqtr3d', STATEMENTS['bvgsu'])
    return w


def bvwbndlem1():
    w = W('bvwbndlem1', 'phiSig ( D ) D^(-2 S) <= 1 / D for squarefree D and S >= 1 (step 1 of W_bound).')
    A = '( %s /\\ %s )' % (HS, SQF('D'))
    st = mkst(w, A)
    hs = st([], 'simpl', HS); sr = st([hs], 'simpld', 'S e. RR'); s1 = st([hs], 'simprd', '1 <_ S')
    s0 = linarith(w, A, [s1], '0 <_ S', leaves={'S': sr})
    sqf = st([], 'simpr', SQF('D')); dnn = st([sqf], 'simpld', 'D e. NN')
    drp = st([dnn], 'nnrpd', 'D e. RR+'); dre = st([drp], 'rpred', 'D e. RR'); dcc = st([drp], 'rpcnd', 'D e. CC'); dne = st([drp], 'rpne0d', 'D =/= 0')
    d1 = sy(w, A, dnn, 'nnge1', '1 <_ D')
    le1 = sy(w, A, st([st([sr, s0], 'jca', HS0), sqf], 'jca', '( %s /\\ %s )' % (HS0, SQF('D'))), 'bvphisgle', '%s <_ ( D ^c S )' % PHS('S', 'D'))
    AP = '( %s /\\ p e. %s )' % (A, PRF('D')); sp = mkst(w, AP)
    pf = prfacts(w, AP, sp([], 'simpr', 'p e. %s' % PRF('D')), 'D')
    cf = cxpfacts(w, AP, pf, lift(w, sr, AP), lift(w, s0, AP))
    phre = st([sy(w, A, dnn, 'pffinq', '%s e. Fin' % PRF('D')), cf['m1re']], 'fprodrecl', '%s e. RR' % PHS('S', 'D'))
    EX = '( -u 2 x. S )'
    cl = Closure(w, A, {'S': sr})
    exr = cl.mem(EX, 'RR')
    E2 = '( D ^c %s )' % EX
    e2rp = st([drp, exr], 'rpcxpcld', '%s e. RR+' % E2)
    dsrp = st([drp, sr], 'rpcxpcld', '( D ^c S ) e. RR+')
    m1 = st([phre, st([dsrp], 'rpred', '( D ^c S ) e. RR'), st([e2rp], 'rpred', '%s e. RR' % E2), st([e2rp], 'rpge0d', '0 <_ %s' % E2), le1], 'lemul1ad',
            '( %s x. %s ) <_ ( ( D ^c S ) x. %s )' % (PHS('S', 'D'), E2, E2))
    sc = st([sr], 'recnd', 'S e. CC')
    ca = st([dcc, dne, sc, st([exr], 'recnd', '%s e. CC' % EX)], 'cxpaddd', '( D ^c ( S + %s ) ) = ( ( D ^c S ) x. %s )' % (EX, E2))
    es = lineq(w, A, '( S + %s )' % EX, '-u S', leaves={'S': sr})
    ca2 = st([st([ca], 'eqcomd', '( ( D ^c S ) x. %s ) = ( D ^c ( S + %s ) )' % (E2, EX)), st([es], 'oveq2d', '( D ^c ( S + %s ) ) = ( D ^c -u S )' % EX)], 'eqtrd',
             '( ( D ^c S ) x. %s ) = ( D ^c -u S )' % E2)
    le2 = st([dre, d1, st([sr], 'renegcld', '-u S e. RR'), cl.mem('-u 1', 'RR'), linarith(w, A, [s1], '-u S <_ -u 1', leaves={'S': sr})], 'cxplead', '( D ^c -u S ) <_ ( D ^c -u 1 )')
    e3 = st([st([dcc, dne, st([], '1cnd', '1 e. CC')], 'cxpnegd', '( D ^c -u 1 ) = ( 1 / ( D ^c 1 ) )'), st([st([dcc], 'cxp1d', '( D ^c 1 ) = D')], 'oveq2d', '( 1 / ( D ^c 1 ) ) = ( 1 / D )')], 'eqtrd',
            '( D ^c -u 1 ) = ( 1 / D )')
    t1 = st([m1, ca2], 'breqtrd', '( %s x. %s ) <_ ( D ^c -u S )' % (PHS('S', 'D'), E2))
    t2 = st([le2, e3], 'breqtrd', '( D ^c -u S ) <_ ( 1 / D )')
    lhsr = st([phre, st([e2rp], 'rpred', '%s e. RR' % E2)], 'remulcld', '( %s x. %s ) e. RR' % (PHS('S', 'D'), E2))
    w.qed([lhsr, st([drp, st([sr], 'renegcld', '-u S e. RR')], 'rpcxpcld', '( D ^c -u S ) e. RR+') and st([st([drp, st([sr], 'renegcld', '-u S e. RR')], 'rpcxpcld', '( D ^c -u S ) e. RR+')], 'rpred', '( D ^c -u S ) e. RR'),
           st([drp], 'rpreccld', '( 1 / D ) e. RR+') and st([st([drp], 'rpreccld', '( 1 / D ) e. RR+')], 'rpred', '( 1 / D ) e. RR'), t1, t2], 'letrd', STATEMENTS['bvwbndlem1'])
    return w


def dvfacts(w, AD, nnn, d, n):
    """under AD with ( AD -> d e. DV(n) ): d e. NN, d || n, ( n / d ) e. NN, ( n / d ) e. DV(n)"""
    st = mkst(w, AD)
    del_ = st([], 'simpr', '%s e. %s' % (d, DV(n)))
    sub = w.s([], 'breq1', '( x = %s -> ( x || %s <-> %s || %s ) )' % (d, n, d, n))
    el = w.s([sub], 'elrab', '( %s e. %s <-> ( %s e. NN /\\ %s || %s ) )' % (d, DV(n), d, d, n))
    both = st([del_, el], 'sylib', '( %s e. NN /\\ %s || %s )' % (d, d, n))
    dnn = st([both], 'simpld', '%s e. NN' % d); ddv = st([both], 'simprd', '%s || %s' % (d, n))
    cel = sy2(w, AD, nnn, del_, 'dvdsdivcl', '( %s / %s ) e. %s' % (n, d, DV(n)))
    sub2 = w.s([], 'breq1', '( x = ( %s / %s ) -> ( x || %s <-> ( %s / %s ) || %s ) )' % (n, d, n, n, d, n))
    el2 = w.s([sub2], 'elrab', '( ( %s / %s ) e. %s <-> ( ( %s / %s ) e. NN /\\ ( %s / %s ) || %s ) )' % (n, d, DV(n), n, d, n, d, n))
    both2 = st([cel, el2], 'sylib', '( ( %s / %s ) e. NN /\\ ( %s / %s ) || %s )' % (n, d, n, d, n))
    return dict(dnn=dnn, ddv=ddv, cnn=st([both2], 'simpld', '( %s / %s ) e. NN' % (n, d)), cdv=st([both2], 'simprd', '( %s / %s ) || %s' % (n, d, n)), del_=del_)


def bvwbndlem2():
    w = W('bvwbndlem2', '( 1 / N ) ( N / phi N )^2 as the divisor sum of ( g-product / d ) ( 1 / ( N / d ) ) with the squarefree '
                        'indicators (step 2 of W_bound).')
    A = SQF('N')
    st = mkst(w, A)
    nnn = st([], 'simpl', 'N e. NN'); mu = st([], 'simpr', '( mmu ` N ) =/= 0')
    ncc = st([nnn], 'nncnd', 'N e. CC'); nne = st([st([nnn], 'nnrpd', 'N e. RR+')], 'rpne0d', 'N =/= 0')
    sqt = w.s([], 'bvsqtot', '( %s -> %s = sum_ d e. %s %s )' % (A, RAT2('N'), DV('N'), PG('d')))
    fin = sy(w, A, nnn, 'dvdsfi', '%s e. Fin' % DV('N'))
    AD = '( %s /\\ d e. %s )' % (A, DV('N')); sd = mkst(w, AD)
    dv = dvfacts(w, AD, lift(w, nnn, AD), 'd', 'N')
    pg = pgfacts(w, AD, dv['dnn'], 'd')
    rn = st([ncc, nne], 'reccld', '( 1 / N ) e. CC')
    mul = st([fin, rn, sd([pg['pre']], 'recnd', '%s e. CC' % PG('d'))], 'fsummulc2', '( ( 1 / N ) x. sum_ d e. %s %s ) = sum_ d e. %s ( ( 1 / N ) x. %s )' % (DV('N'), PG('d'), DV('N'), PG('d')))
    # termwise
    nnd = lift(w, nnn, AD)
    mud = sd([bind3(w, AD, nnd, dv['dnn'], dv['ddv'], 'N e. NN', 'd e. NN', 'd || N'), w.inst('dvdssqf')], 'syl', '( ( mmu ` N ) =/= 0 -> ( mmu ` d ) =/= 0 )') if False else None
    mud = sd([lift(w, mu, AD), w.s([bind3(w, AD, nnd, dv['dnn'], dv['ddv'], 'N e. NN', 'd e. NN', 'd || N'), w.inst('dvdssqf')], 'syl', '( %s -> ( ( mmu ` N ) =/= 0 -> ( mmu ` d ) =/= 0 ) )' % AD)], 'mpd', '( mmu ` d ) =/= 0')
    muc = sd([lift(w, mu, AD), w.s([bind3(w, AD, nnd, dv['cnn'], dv['cdv'], 'N e. NN', '( N / d ) e. NN', '( N / d ) || N'), w.inst('dvdssqf')], 'syl',
                                    '( %s -> ( ( mmu ` N ) =/= 0 -> ( mmu ` ( N / d ) ) =/= 0 ) )' % AD)], 'mpd', '( mmu ` ( N / d ) ) =/= 0')
    i1 = sd([mud], 'iftrued', '%s = ( %s / d )' % (IFF('d'), PG('d')))
    i2 = sd([muc], 'iftrued', '%s = ( 1 / ( N / d ) )' % IFG('( N / d )'))
    dcc = sd([dv['dnn']], 'nncnd', 'd e. CC'); dne = sd([sd([dv['dnn']], 'nnrpd', 'd e. RR+')], 'rpne0d', 'd =/= 0')
    pgc = sd([pg['pre']], 'recnd', '%s e. CC' % PG('d'))
    ncd = lift(w, ncc, AD); nned = lift(w, nne, AD)
    rd = sd([ncd, dcc, nned, dne], 'recdivd', '( 1 / ( N / d ) ) = ( d / N )')
    Q = '( %s / d )' % PG('d')
    f1 = sd([i1, sd([i2, rd], 'eqtrd', '%s = ( d / N )' % IFG('( N / d )'))], 'oveq12d', '( %s x. %s ) = ( %s x. ( d / N ) )' % (IFF('d'), IFG('( N / d )'), Q))
    f2 = sd([sd([pgc, dcc, dne], 'divcld', '%s e. CC' % Q), sd([dcc, ncd, nned], 'divcld', '( d / N ) e. CC')], 'mulcomd', '( %s x. ( d / N ) ) = ( ( d / N ) x. %s )' % (Q, Q))
    f3 = sd([pgc, dcc, ncd, dne, nned], 'dmdcand', '( ( d / N ) x. %s ) = ( %s / N )' % (Q, PG('d')))
    f4 = sd([pgc, ncd, nned], 'divrec2d', '( %s / N ) = ( ( 1 / N ) x. %s )' % (PG('d'), PG('d')))
    term = eqtr(w, AD, [f1, f2, f3, f4], None)
    tsum = st([sd([term], 'eqcomd', '( ( 1 / N ) x. %s ) = ( %s x. %s )' % (PG('d'), IFF('d'), IFG('( N / d )')))], 'sumeq2dv',
              'sum_ d e. %s ( ( 1 / N ) x. %s ) = sum_ d e. %s ( %s x. %s )' % (DV('N'), PG('d'), DV('N'), IFF('d'), IFG('( N / d )')))
    full = eqtr(w, A, [st([sqt], 'oveq2d', '( ( 1 / N ) x. %s ) = ( ( 1 / N ) x. sum_ d e. %s %s )' % (RAT2('N'), DV('N'), PG('d'))), mul, tsum], None)
    w.qed([full], 'id', STATEMENTS['bvwbndlem2']) if False else w.qed([full, w.inst('id')], 'syl', STATEMENTS['bvwbndlem2'])
    return w


def bvwbndlem3():
    w = W('bvwbndlem3', 'The hyperbola step of W_bound: sum_ n <= M sum_ d || n f(d) g(n/d) <= ( sum_ d <= M f(d) ) ( 1 + log M ) '
                        '(dvdsflsumcom, harmub).')
    A = 'M e. NN'
    st = mkst(w, A)
    mnn = w.s([], 'id', '( %s -> M e. NN )' % A)
    mre = st([mnn], 'nnred', 'M e. RR'); mz = st([mnn], 'nnzd', 'M e. ZZ')
    fl = sy(w, A, mz, 'flid', '( |_ ` M ) = M')
    FM = '( |_ ` M )'
    Bn = '( %s x. %s )' % (IFF('d'), IFG('( n / d )'))
    Cm = '( %s x. %s )' % (IFF('d'), IFG('( ( d x. m ) / d )'))
    idn = w.s([], 'id', '( n = ( d x. m ) -> n = ( d x. m ) )')
    cg, newc = w.congr(Bn, {'n': '( d x. m )'}, 'n = ( d x. m )', {'n': idn})
    assert newc == Cm, newc
    # closure of B
    AB = '( %s /\\ ( n e. ( 1 ... %s ) /\\ d e. %s ) )' % (A, FM, DV('n')); sb = mkst(w, AB)
    nnb = sy(w, AB, sb([], 'simprl', 'n e. ( 1 ... %s )' % FM), 'elfznn', 'n e. NN')
    ADB = '( %s /\\ d e. %s )' % ('( %s /\\ n e. ( 1 ... %s ) )' % (A, FM), DV('n'))
    # restate AB's facts through a conjunction-free route: derive d e. DV(n) and use dvfacts on an AB-shaped ante
    delb = sb([], 'simprr', 'd e. %s' % DV('n'))
    sub = w.s([], 'breq1', '( x = d -> ( x || n <-> d || n ) )')
    el = w.s([sub], 'elrab', '( d e. %s <-> ( d e. NN /\\ d || n ) )' % DV('n'))
    dnnb = sb([sb([delb, el], 'sylib', '( d e. NN /\\ d || n )')], 'simpld', 'd e. NN')
    cel = sy2(w, AB, nnb, delb, 'dvdsdivcl', '( n / d ) e. %s' % DV('n'))
    cnnb = sy(w, AB, cel, 'elrabi', '( n / d ) e. NN')
    pgb = pgfacts(w, AB, dnnb, 'd'); igb = igfacts(w, AB, cnnb, '( n / d )')
    bcc = sb([pgb['ifcc'], igb['ifcc']], 'mulcld', '%s e. CC' % Bn)
    dfc = w.s([cg, mre, bcc], 'dvdsflsumcom', '( %s -> sum_ n e. ( 1 ... %s ) sum_ d e. %s %s = sum_ d e. ( 1 ... %s ) sum_ m e. ( 1 ... ( |_ ` ( M / d ) ) ) %s )'
              % (A, FM, DV('n'), Bn, FM, Cm))
    rw1, l1 = w.rewrite('sum_ n e. ( 1 ... %s ) sum_ d e. %s %s' % (FM, DV('n'), Bn), {FM: ('M', fl)}, A)
    rw2, r2 = w.rewrite('sum_ d e. ( 1 ... %s ) sum_ m e. ( 1 ... ( |_ ` ( M / d ) ) ) %s' % (FM, Cm), {FM: ('M', fl)}, A)
    LHS0 = 'sum_ n e. ( 1 ... M ) sum_ d e. %s %s' % (DV('n'), Bn)
    assert l1 == LHS0, l1
    eq = eqtr(w, A, [st([rw1], 'eqcomd', '%s = sum_ n e. ( 1 ... %s ) sum_ d e. %s %s' % (LHS0, FM, DV('n'), Bn)), dfc, rw2], None)
    # termwise over d e. ( 1 ... M )
    AD = '( %s /\\ d e. ( 1 ... M ) )' % A; sd = mkst(w, AD)
    del_ = sd([], 'simpr', 'd e. ( 1 ... M )')
    dnn = sy(w, AD, del_, 'elfznn', 'd e. NN')
    dcc = sd([dnn], 'nncnd', 'd e. CC'); dne = sd([sd([dnn], 'nnrpd', 'd e. RR+')], 'rpne0d', 'd =/= 0')
    pg = pgfacts(w, AD, dnn, 'd')
    FLD = '( |_ ` ( M / d ) )'
    AM = '( %s /\\ m e. ( 1 ... %s ) )' % (AD, FLD); sm = mkst(w, AM)
    mnn2 = sy(w, AM, sm([], 'simpr', 'm e. ( 1 ... %s )' % FLD), 'elfznn', 'm e. NN')
    mcc = sm([mnn2], 'nncnd', 'm e. CC')
    dc3 = sm([mcc, lift(w, dcc, AM), lift(w, dne, AM)], 'divcan3d', '( ( d x. m ) / d ) = m')
    rw3, c3 = w.rewrite(Cm, {'( ( d x. m ) / d )': ('m', dc3)}, AM)
    Cm2 = '( %s x. %s )' % (IFF('d'), IFG('m'))
    assert c3 == Cm2, c3
    ig = igfacts(w, AM, mnn2, 'm')
    finm = sd([], 'fzfid', '( 1 ... %s ) e. Fin' % FLD)
    SIG = 'sum_ m e. ( 1 ... %s ) %s' % (FLD, IFG('m'))
    SH = 'sum_ m e. ( 1 ... %s ) ( 1 / m )' % FLD
    fm = sd([finm, pg['ifcc'], ig['ifcc']], 'fsummulc2', '( %s x. %s ) = sum_ m e. ( 1 ... %s ) %s' % (IFF('d'), SIG, FLD, Cm2))
    inner = sd([sd([rw3], 'sumeq2dv', 'sum_ m e. ( 1 ... %s ) %s = sum_ m e. ( 1 ... %s ) %s' % (FLD, Cm, FLD, Cm2)), sd([fm], 'eqcomd', 'sum_ m e. ( 1 ... %s ) %s = ( %s x. %s )' % (FLD, Cm2, IFF('d'), SIG))], 'eqtrd',
               'sum_ m e. ( 1 ... %s ) %s = ( %s x. %s )' % (FLD, Cm, IFF('d'), SIG))
    sigre = sd([finm, ig['ifre']], 'fsumrecl', '%s e. RR' % SIG)
    shre = sd([finm, ig['rr']], 'fsumrecl', '%s e. RR' % SH)
    sle = sd([finm, ig['ifre'], ig['rr'], ig['ifle']], 'fsumle', '%s <_ %s' % (SIG, SH))
    hb = sy(w, AD, bind(w, AD, lift(w, mnn, AD), del_, 'M e. NN', 'd e. ( 1 ... M )'), 'harmub', '%s <_ ( 1 + ( log ` M ) )' % SH)
    logre = sd([lift(w, st([mnn], 'nnrpd', 'M e. RR+'), AD)], 'relogcld', '( log ` M ) e. RR')
    LR = sd([sd([], '1red', '1 e. RR'), logre], 'readdcld', '%s e. RR' % LOGM)
    s2 = sd([sigre, shre, LR, sle, hb], 'letrd', '%s <_ %s' % (SIG, LOGM))
    s3 = sd([sigre, LR, pg['ifre'], pg['if0'], s2], 'lemul2ad', '( %s x. %s ) <_ ( %s x. %s )' % (IFF('d'), SIG, IFF('d'), LOGM))
    tle = sd([inner, s3], 'eqbrtrd', 'sum_ m e. ( 1 ... %s ) %s <_ ( %s x. %s )' % (FLD, Cm, IFF('d'), LOGM))
    # closure of the inner sum
    cmre = sm([pg['ifre'] if False else lift(w, pg['ifre'], AM), ig['ifre']], 'remulcld', '%s e. RR' % Cm2)
    cmre0 = sm([rw3, cmre], 'eqeltrrd', '%s e. RR' % Cm) if False else sm([sm([rw3], 'eqcomd', '%s = %s' % (Cm2, Cm)), cmre], 'eqeltrrd', '%s e. RR' % Cm)
    innre = sd([finm, cmre0], 'fsumrecl', 'sum_ m e. ( 1 ... %s ) %s e. RR' % (FLD, Cm))
    fin1 = st([], 'fzfid', '( 1 ... M ) e. Fin')
    tot = st([fin1, innre, sd([pg['ifre'], LR], 'remulcld', '( %s x. %s ) e. RR' % (IFF('d'), LOGM)), tle], 'fsumle',
             '%s <_ sum_ d e. ( 1 ... M ) ( %s x. %s )' % (r2, IFF('d'), LOGM))
    LRA = lift(w, LR, AD) if False else None
    logreA = st([st([mnn], 'nnrpd', 'M e. RR+')], 'relogcld', '( log ` M ) e. RR')
    LRa = st([st([], '1red', '1 e. RR'), logreA], 'readdcld', '%s e. RR' % LOGM)
    fm1 = st([fin1, st([LRa], 'recnd', '%s e. CC' % LOGM), pg['ifcc']], 'fsummulc1', '( sum_ d e. ( 1 ... M ) %s x. %s ) = sum_ d e. ( 1 ... M ) ( %s x. %s )' % (IFF('d'), LOGM, IFF('d'), LOGM))
    tot2 = st([tot, st([fm1], 'eqcomd', 'sum_ d e. ( 1 ... M ) ( %s x. %s ) = ( sum_ d e. ( 1 ... M ) %s x. %s )' % (IFF('d'), LOGM, IFF('d'), LOGM))], 'breqtrd',
              '%s <_ ( sum_ d e. ( 1 ... M ) %s x. %s )' % (r2, IFF('d'), LOGM))
    w.qed([eq, tot2], 'eqbrtrd', STATEMENTS['bvwbndlem3'])
    return w


def bvwbndlem4():
    w = W('bvwbndlem4', 'sum_ d <= M mu^2 ( d ) prod_ p || d g(p) / d <= 8 (the hC step of W_bound: bvgsu, bvsqfsum at u, bvuprod).')
    A = 'M e. NN'
    st = mkst(w, A)
    mnn = w.s([], 'id', '( %s -> M e. NN )' % A)
    Wf = '( t e. NN |-> %s )' % U('t')
    # hypotheses of bvsqfsum
    A2 = '( %s /\\ n e. ( 2 ... M ) )' % A; s2 = mkst(w, A2)
    nel = s2([], 'simpr', 'n e. ( 2 ... M )')
    nz = sy(w, A2, nel, 'elfzelz', 'n e. ZZ'); nre = s2([nz], 'zred', 'n e. RR')
    n2 = sy(w, A2, nel, 'elfzle1', '2 <_ n')
    nnn = s2([nz, linarith(w, A2, [n2], '0 < n', leaves={'n': nre})], 'elnnz1d' if False else 'elnnzd', 'n e. NN') if False else None
    nnn = sy(w, A2, bind(w, A2, nz, linarith(w, A2, [n2], '0 < n', leaves={'n': nre}), 'n e. ZZ', '0 < n'), 'elnnz', 'n e. NN') if False else \
        s2([bind(w, A2, nz, linarith(w, A2, [n2], '0 < n', leaves={'n': nre}), 'n e. ZZ', '0 < n'), w.s([], 'elnnz', '( n e. NN <-> ( n e. ZZ /\\ 0 < n ) )')], 'sylibr', 'n e. NN')
    uf = ufacts(w, A2, nre, n2, 'n')
    vn, _ = mpv(w, A2, 't', 'NN', U('t'), 'n', nnn, exs=w.s([], 'ovexd', '( %s -> %s e. _V )' % (A2, U('n'))))
    wre = s2([vn, uf['ure']], 'eqeltrd', '( %s ` n ) e. RR' % Wf)
    w0 = s2([uf['u0'], vn], 'breqtrrd', '0 <_ ( %s ` n )' % Wf)
    sq = w.s([mnn, wre, w0], 'bvsqfsum', '( %s -> sum_ a e. ( 1 ... M ) if ( ( mmu ` a ) =/= 0 , prod_ p e. %s ( %s ` p ) , 0 ) <_ prod_ n e. ( 2 ... M ) ( 1 + ( %s ` n ) ) )'
             % (A, PRF('a'), Wf, Wf))
    # right side: prod ( 1 + W n ) = prod ( 1 + u n ) <= 8
    PU = 'prod_ n e. ( 2 ... M ) ( 1 + %s )' % U('n')
    req = st([s2([vn], 'oveq2d', '( 1 + ( %s ` n ) ) = ( 1 + %s )' % (Wf, U('n')))], 'prodeq2dv', 'prod_ n e. ( 2 ... M ) ( 1 + ( %s ` n ) ) = %s' % (Wf, PU))
    b8 = w.s([], 'bvuprod', STATEMENTS['bvuprod'])
    # left side: termwise, for a e. ( 1 ... M )
    AA = '( %s /\\ a e. ( 1 ... M ) )' % A; sa = mkst(w, AA)
    ann = sy(w, AA, sa([], 'simpr', 'a e. ( 1 ... M )'), 'elfznn', 'a e. NN')
    AT = '( %s /\\ ( mmu ` a ) =/= 0 )' % AA; stt = mkst(w, AT)
    ATP = '( %s /\\ p e. %s )' % (AT, PRF('a')); sp = mkst(w, ATP)
    pf = prfacts(w, ATP, sp([], 'simpr', 'p e. %s' % PRF('a')), 'a')
    vp, _ = mpv(w, ATP, 't', 'NN', U('t'), 'p', pf['nn'], exs=w.s([], 'ovexd', '( %s -> %s e. _V )' % (ATP, U('p'))))
    pw = stt([vp], 'prodeq2dv', 'prod_ p e. %s ( %s ` p ) = prod_ p e. %s %s' % (PRF('a'), Wf, PRF('a'), U('p')))
    gsu = sy(w, AT, bind(w, AT, lift(w, ann, AT), stt([], 'simpr', '( mmu ` a ) =/= 0'), 'a e. NN', '( mmu ` a ) =/= 0'), 'bvgsu',
             STATEMENTS['bvgsu'].split(' -> ', 1)[1][:-2].replace(' A ', ' a ').replace('q || A }', 'q || a }'))
    br = stt([pw, stt([gsu], 'eqcomd', 'prod_ p e. %s %s = ( %s / a )' % (PRF('a'), U('p'), PG('a')))], 'eqtrd', 'prod_ p e. %s ( %s ` p ) = ( %s / a )' % (PRF('a'), Wf, PG('a')))
    ife = w.s([br], 'ifeq1da', '( %s -> if ( ( mmu ` a ) =/= 0 , prod_ p e. %s ( %s ` p ) , 0 ) = %s )' % (AA, PRF('a'), Wf, IFF('a')))
    SW = 'sum_ a e. ( 1 ... M ) if ( ( mmu ` a ) =/= 0 , prod_ p e. %s ( %s ` p ) , 0 )' % (PRF('a'), Wf)
    SA = 'sum_ a e. ( 1 ... M ) %s' % IFF('a')
    se = st([ife], 'sumeq2dv', '%s = %s' % (SW, SA))
    ida = w.s([], 'id', '( a = d -> a = d )')
    cba, newd = w.congr(IFF('a'), {'a': 'd'}, 'a = d', {'a': ida})
    cb = st([w.s([cba], 'cbvsumv', '%s = sum_ d e. ( 1 ... M ) %s' % (SA, IFF('d')))], 'a1i', '%s = sum_ d e. ( 1 ... M ) %s' % (SA, IFF('d')))
    lhs = st([st([se], 'eqcomd', '%s = %s' % (SA, SW)), sq], 'eqbrtrd', '%s <_ prod_ n e. ( 2 ... M ) ( 1 + ( %s ` n ) )' % (SA, Wf))
    lhs2 = st([lhs, req], 'breqtrd', '%s <_ %s' % (SA, PU))
    # closures for letrd
    pgA = pgfacts(w, AA, ann, 'a')
    sar = st([st([], 'fzfid', '( 1 ... M ) e. Fin'), pgA['ifre']], 'fsumrecl', '%s e. RR' % SA)
    pur = st([st([], 'fzfid', '( 2 ... M ) e. Fin'), uf['xre']], 'fprodrecl', '%s e. RR' % PU)
    t = st([sar, pur, st([], '8re', '8 e. RR') if False else st([num.re_nat(w, 8)], 'a1i', '8 e. RR'), lhs2, sy(w, A, mnn, 'bvuprod', '%s <_ 8' % PU)], 'letrd', '%s <_ 8' % SA)
    w.qed([st([cb], 'eqcomd', 'sum_ d e. ( 1 ... M ) %s = %s' % (IFF('d'), SA)), t], 'eqbrtrd', STATEMENTS['bvwbndlem4'])
    return w


def bvwbnd():
    w = W('bvwbnd', 'W_bound: sum_ n <= M mu^2 phiSig ( n ) n^(-2 S) ( n / phi n )^2 <= 8 ( 1 + log M ) for S >= 1 (Lean W_bound).')
    A = '( %s /\\ M e. NN )' % HS
    st = mkst(w, A)
    hs = st([], 'simpl', HS); mnn = st([], 'simpr', 'M e. NN')
    sr = st([hs], 'simpld', 'S e. RR'); s1 = st([hs], 'simprd', '1 <_ S')
    s0 = linarith(w, A, [s1], '0 <_ S', leaves={'S': sr})
    fin1 = st([], 'fzfid', '( 1 ... M ) e. Fin')
    AN = '( %s /\\ n e. ( 1 ... M ) )' % A; sn = mkst(w, AN)
    nnn = sy(w, AN, sn([], 'simpr', 'n e. ( 1 ... M )'), 'elfznn', 'n e. NN')
    nrp = sn([nnn], 'nnrpd', 'n e. RR+')
    SD = 'sum_ d e. %s ( %s x. %s )' % (DV('n'), IFF('d'), IFG('( n / d )'))
    find = sy(w, AN, nnn, 'dvdsfi', '%s e. Fin' % DV('n'))
    AND = '( %s /\\ d e. %s )' % (AN, DV('n')); snd = mkst(w, AND)
    dv = dvfacts(w, AND, lift(w, nnn, AND), 'd', 'n')
    pgd = pgfacts(w, AND, dv['dnn'], 'd'); igd = igfacts(w, AND, dv['cnn'], '( n / d )')
    tre = snd([pgd['ifre'], igd['ifre']], 'remulcld', '( %s x. %s ) e. RR' % (IFF('d'), IFG('( n / d )')))
    t0 = snd([pgd['ifre'], igd['ifre'], pgd['if0'], igd['if0']], 'mulge0d', '0 <_ ( %s x. %s )' % (IFF('d'), IFG('( n / d )')))
    sdre = sn([find, tre], 'fsumrecl', '%s e. RR' % SD)
    sd0 = sn([find, tre, t0], 'fsumge0', '0 <_ %s' % SD)
    # the branch value under mu =/= 0
    C = '( mmu ` n ) =/= 0'
    ANT = '( %s /\\ %s )' % (AN, C); snt = mkst(w, ANT)
    sqfn = bind(w, ANT, lift(w, nnn, ANT), snt([], 'simpr', C), 'n e. NN', C)
    E2 = '( n ^c ( -u 2 x. S ) )'
    V = '( ( %s x. %s ) x. %s )' % (PHS('S', 'n'), E2, RAT2('n'))
    l1 = sy(w, ANT, bind(w, ANT, lift(w, hs, ANT), sqfn, HS, SQF('n')), 'bvwbndlem1', '( %s x. %s ) <_ ( 1 / n )' % (PHS('S', 'n'), E2))
    l2 = sy(w, ANT, sqfn, 'bvwbndlem2', '( ( 1 / n ) x. %s ) = %s' % (RAT2('n'), SD))
    # closures
    ANP = '( %s /\\ p e. %s )' % (ANT, PRF('n')); snp = mkst(w, ANP)
    pf = prfacts(w, ANP, snp([], 'simpr', 'p e. %s' % PRF('n')), 'n')
    cf = cxpfacts(w, ANP, pf, lift(w, sr, ANP), lift(w, s0, ANP))
    phre = snt([sy(w, ANT, lift(w, nnn, ANT), 'pffinq', '%s e. Fin' % PRF('n')), cf['m1re']], 'fprodrecl', '%s e. RR' % PHS('S', 'n'))
    cl = Closure(w, ANT, {'S': lift(w, sr, ANT)})
    e2re = snt([snt([lift(w, nrp, ANT), cl.mem('( -u 2 x. S )', 'RR')], 'rpcxpcld', '%s e. RR+' % E2)], 'rpred', '%s e. RR' % E2)
    nphi = sy(w, ANT, lift(w, nnn, ANT), 'phicl', '( phi ` n ) e. NN')
    ratre = snt([snt([lift(w, nnn, ANT)], 'nnred', 'n e. RR'), snt([nphi], 'nnrpd', '( phi ` n ) e. RR+')], 'rerpdivcld', '( n / ( phi ` n ) ) e. RR')
    r2re = snt([ratre], 'resqcld', '%s e. RR' % RAT2('n'))
    r20 = snt([ratre], 'sqge0d', '0 <_ %s' % RAT2('n'))
    m = snt([snt([phre, e2re], 'remulcld', '( %s x. %s ) e. RR' % (PHS('S', 'n'), E2)), snt([lift(w, nrp, ANT)], 'rpreccld', '( 1 / n ) e. RR+') and
             snt([snt([lift(w, nrp, ANT)], 'rpreccld', '( 1 / n ) e. RR+')], 'rpred', '( 1 / n ) e. RR'), r2re, r20, l1], 'lemul1ad', '%s <_ ( ( 1 / n ) x. %s )' % (V, RAT2('n')))
    vle = snt([m, l2], 'breqtrd', '%s <_ %s' % (V, SD))
    c1 = w.s([], 'breq1', '( %s = %s -> ( %s <_ %s <-> %s <_ %s ) )' % (V, WTERM('n'), V, SD, WTERM('n'), SD))
    c2 = w.s([], 'breq1', '( 0 = %s -> ( 0 <_ %s <-> %s <_ %s ) )' % (WTERM('n'), SD, WTERM('n'), SD))
    ANF = '( %s /\\ -. %s )' % (AN, C)
    wle = w.s([c1, c2, vle, lift(w, sd0, ANF)], 'ifbothda', '( %s -> %s <_ %s )' % (AN, WTERM('n'), SD))
    vre = snt([snt([phre, e2re], 'remulcld', '( %s x. %s ) e. RR' % (PHS('S', 'n'), E2)), r2re], 'remulcld', '%s e. RR' % V)
    wre = sn([vre, w.s([], '0red', '( %s -> 0 e. RR )' % ANF)], 'ifclda', '%s e. RR' % WTERM('n'))
    s1le = st([fin1, wre, sdre, wle], 'fsumle', 'sum_ n e. ( 1 ... M ) %s <_ sum_ n e. ( 1 ... M ) %s' % (WTERM('n'), SD))
    l3 = sy(w, A, mnn, 'bvwbndlem3', STATEMENTS['bvwbndlem3'].split(' -> ', 1)[1][:-2])
    l4 = sy(w, A, mnn, 'bvwbndlem4', STATEMENTS['bvwbndlem4'].split(' -> ', 1)[1][:-2])
    SF = 'sum_ d e. ( 1 ... M ) %s' % IFF('d')
    AD = '( %s /\\ d e. ( 1 ... M ) )' % A
    pga = pgfacts(w, AD, sy(w, AD, mkst(w, AD)([], 'simpr', 'd e. ( 1 ... M )'), 'elfznn', 'd e. NN'), 'd')
    sfr = st([fin1, pga['ifre']], 'fsumrecl', '%s e. RR' % SF)
    mrp = st([mnn], 'nnrpd', 'M e. RR+')
    lg0 = st([st([mrp], 'rpred', 'M e. RR'), sy(w, A, mnn, 'nnge1', '1 <_ M')], 'logge0d', '0 <_ ( log ` M )')
    LR = st([st([], '1red', '1 e. RR'), st([mrp], 'relogcld', '( log ` M ) e. RR')], 'readdcld', '%s e. RR' % LOGM)
    L0 = linarith(w, A, [lg0], '0 <_ %s' % LOGM, leaves={'( log ` M )': st([mrp], 'relogcld', '( log ` M ) e. RR')})
    m8 = st([sfr, st([num.re_nat(w, 8)], 'a1i', '8 e. RR'), LR, L0, l4], 'lemul1ad', '( %s x. %s ) <_ ( 8 x. %s )' % (SF, LOGM, LOGM))
    sdt = st([fin1, sdre], 'fsumrecl', 'sum_ n e. ( 1 ... M ) %s e. RR' % SD)
    wt = st([fin1, wre], 'fsumrecl', 'sum_ n e. ( 1 ... M ) %s e. RR' % WTERM('n'))
    r1 = st([sfr, LR], 'remulcld', '( %s x. %s ) e. RR' % (SF, LOGM))
    r8 = st([st([num.re_nat(w, 8)], 'a1i', '8 e. RR'), LR], 'remulcld', '( 8 x. %s ) e. RR' % LOGM)
    t1 = st([wt, sdt, r1, s1le, l3], 'letrd', 'sum_ n e. ( 1 ... M ) %s <_ ( %s x. %s )' % (WTERM('n'), SF, LOGM))
    w.qed([wt, r1, r8, t1, m8], 'letrd', STATEMENTS['bvwbnd'])
    return w


if __name__ == '__main__':
    for f in sys.argv[1:] or ['bvsqtot', 'bvgsu', 'bvwbndlem1', 'bvwbndlem2', 'bvwbndlem3', 'bvwbndlem4', 'bvwbnd']:
        globals()[f]().run()
