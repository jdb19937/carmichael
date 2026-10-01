"""Sortie z4c: lswinset (Lean hset, the used inclusion), lswinw (Lean hstep1), lswsieve (window_sieve)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from tm import W
from z4clib import STATEMENTS as S, TS, RF, Q0, Q0S
from z4c_a import mk, a1
from z4c_b import elrabst


def tc(r, F='f'):
    return '( ( mmu ` %s ) =/= 0 /\\ ( %s gcd %s ) = 1 )' % (r, r, F)


def tceq(w, a, b, F='f'):
    m = w.s([w.s([], 'fveq2', '( %s = %s -> ( mmu ` %s ) = ( mmu ` %s ) )' % (a, b, a, b))], 'neeq1d',
            '( %s = %s -> ( ( mmu ` %s ) =/= 0 <-> ( mmu ` %s ) =/= 0 ) )' % (a, b, a, b))
    g = w.s([w.s([], 'oveq1', '( %s = %s -> ( %s gcd %s ) = ( %s gcd %s ) )' % (a, b, a, F, b, F))], 'eqeq1d',
            '( %s = %s -> ( ( %s gcd %s ) = 1 <-> ( %s gcd %s ) = 1 ) )' % (a, b, a, F, b, F))
    return w.s([m, g], 'anbi12d', '( %s = %s -> ( %s <-> %s ) )' % (a, b, tc(a, F), tc(b, F)))


def rfc(r):
    return '( ( %s x. f ) <_ %s /\\ %s )' % (r, Q0, tc(r))


def rfceq(w, a, b):
    e = w.s([w.s([], 'oveq1', '( %s = %s -> ( %s x. f ) = ( %s x. f ) )' % (a, b, a, b))], 'breq1d',
            '( %s = %s -> ( ( %s x. f ) <_ %s <-> ( %s x. f ) <_ %s ) )' % (a, b, a, Q0, b, Q0))
    return w.s([e, tceq(w, a, b)], 'anbi12d', '( %s = %s -> ( %s <-> %s ) )' % (a, b, rfc(a), rfc(b)))


QF = '( |_ ` ( Q / f ) )'


def lswinset():
    w = W('lswinset', "The squarefree r <_ Q / f coprime to f are among Lean's r-range RF at conductor f "
          '(the used half of window_sieve hset).')
    AW = '( Q e. RR /\\ f e. %s )' % Q0S
    TSQ = TS(QF, 'f')
    RFQ = RF(Q0)
    FZq = '( 1 ... %s )' % QF
    AY = '( %s /\\ y e. %s )' % (AW, TSQ)
    s = mk(w, AY)
    qre = s([], 'simpll', 'Q e. RR')
    ffz = s([], 'simplr', 'f e. %s' % Q0S)
    fnn = s([ffz, w.inst('elfznn')], 'syl', 'f e. NN')
    fre = s([fnn], 'nnred', 'f e. RR')
    fpos = s([fnn], 'nngt0d', '0 < f')
    qfre = s([qre, fre, s([fnn], 'nnne0d', 'f =/= 0')], 'redivcld', '( Q / f ) e. RR')
    yc = elrabst(w, AY, s([], 'simpr', 'y e. %s' % TSQ), 'r', 'y', FZq, tc('r'), tc('y'), tceq(w, 'r', 'y'))
    yfz = s([yc], 'simpld', 'y e. %s' % FZq)
    ynn = s([yfz, w.inst('elfznn')], 'syl', 'y e. NN')
    yre = s([ynn], 'nnred', 'y e. RR')
    yle = s([yfz, w.inst('elfzle2')], 'syl', 'y <_ %s' % QF)
    flq = s([qfre, w.inst('flle')], 'syl', '%s <_ ( Q / f )' % QF)
    yleq = s([yre, s([s([qfre], 'flcld', '%s e. ZZ' % QF)], 'zred', '%s e. RR' % QF),
              qfre, yle, flq], 'letrd', 'y <_ ( Q / f )')
    yfq = s([s([yre, qre, s([fre, fpos], 'jca', '( f e. RR /\\ 0 < f )'), w.inst('lemuldiv')], 'syl3anc',
               '( ( y x. f ) <_ Q <-> y <_ ( Q / f ) )'), yleq], 'mpbird', '( y x. f ) <_ Q')
    yfnn = s([ynn, fnn], 'nnmulcld', '( y x. f ) e. NN')
    yf0 = s([s([qre, s([yfnn], 'nnzd', '( y x. f ) e. ZZ'), w.inst('flge')], 'syl2anc',
               '( ( y x. f ) <_ Q <-> ( y x. f ) <_ %s )' % Q0),
             yfq], 'mpbid', '( y x. f ) <_ %s' % Q0)
    yyf = s([s([yre, fre], 'jca', '( y e. RR /\\ f e. RR )'),
             s([s([yre, s([ynn], 'nngt0d', '0 < y')], 'ltled', '0 <_ y'),
                s([fnn], 'nnge1d', '1 <_ f')], 'jca', '( 0 <_ y /\\ 1 <_ f )'), w.inst('lemulge11')], 'syl2anc',
            'y <_ ( y x. f )')
    q0z = s([qre], 'flcld', '%s e. ZZ' % Q0)
    yq0 = s([yre, s([yfnn], 'nnred', '( y x. f ) e. RR'), s([q0z], 'zred', '%s e. RR' % Q0), yyf, yf0], 'letrd',
            'y <_ %s' % Q0)
    yfz0 = s([s([q0z, w.inst('fznn')], 'syl', '( y e. %s <-> ( y e. NN /\\ y <_ %s ) )' % (Q0S, Q0)),
              s([ynn, yq0], 'jca', '( y e. NN /\\ y <_ %s )' % Q0)], 'mpbird', 'y e. %s' % Q0S)
    elR = w.s([rfceq(w, 'r', 'y')], 'elrab', '( y e. %s <-> ( y e. %s /\\ %s ) )' % (RFQ, Q0S, rfc('y')))
    yR = s([s([elR], 'a1i', '( y e. %s <-> ( y e. %s /\\ %s ) )' % (RFQ, Q0S, rfc('y'))),
            s([yfz0, s([yf0, s([yc], 'simprd', tc('y'))], 'jca', rfc('y'))], 'jca', '( y e. %s /\\ %s )' % (Q0S, rfc('y')))],
           'mpbird', 'y e. %s' % RFQ)
    ex = w.s([yR], 'ex', '( %s -> ( y e. %s -> y e. %s ) )' % (AW, TSQ, RFQ))
    w.qed([ex], 'ssrdv', S['lswinset'])
    return w


def lswinw():
    w = W('lswinw', 'The log weight at conductor f is dominated by the totient-quotient sum over '
          "Lean's r-range (Lean window_sieve hstep1).")
    AW3 = '( ( Q e. RR /\\ 2 <_ Q ) /\\ f e. %s /\\ ( B e. RR /\\ 0 <_ B ) )' % Q0S
    st = mk(w, AW3)
    TSQ = TS(QF, 'f')
    RFQ = RF(Q0)
    q2 = st([], 'simp1', '( Q e. RR /\\ 2 <_ Q )')
    qre = st([q2], 'simpld', 'Q e. RR')
    ffz = st([], 'simp2', 'f e. %s' % Q0S)
    bb = st([], 'simp3', '( B e. RR /\\ 0 <_ B )')
    bre = st([bb], 'simpld', 'B e. RR')
    bge = st([bb], 'simprd', '0 <_ B')
    fnn = st([ffz, w.inst('elfznn')], 'syl', 'f e. NN')
    fre = st([fnn], 'nnred', 'f e. RR')
    frp = st([fnn], 'nnrpd', 'f e. RR+')
    fc = st([fnn], 'nncnd', 'f e. CC')
    fne = st([fnn], 'nnne0d', 'f =/= 0')
    q0re = st([st([qre], 'flcld', '%s e. ZZ' % Q0)], 'zred', '%s e. RR' % Q0)
    fq = st([fre, q0re, qre, st([ffz, w.inst('elfzle2')], 'syl', 'f <_ %s' % Q0),
             st([qre, w.inst('flle')], 'syl', '%s <_ Q' % Q0)], 'letrd', 'f <_ Q')
    one = st([], '1red', '1 e. RR')
    q1 = st([st([one, qre, st([fre, st([fnn], 'nngt0d', '0 < f')], 'jca', '( f e. RR /\\ 0 < f )'), w.inst('lemuldiv')],
                'syl3anc', '( ( 1 x. f ) <_ Q <-> 1 <_ ( Q / f ) )'),
             st([st([fc], 'mullidd', '( 1 x. f ) = f'), fq], 'eqbrtrd', '( 1 x. f ) <_ Q')], 'mpbid', '1 <_ ( Q / f )')
    qfre = st([qre, fre, fne], 'redivcld', '( Q / f ) e. RR')
    qpos = st([st([], '0red', '0 e. RR'), st([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR'), qre,
               st([w.s([], '2pos', '0 < 2')], 'a1i', '0 < 2'), st([q2], 'simprd', '2 <_ Q')], 'ltletrd', '0 < Q')
    qfrp = st([st([qre, qpos], 'elrpd', 'Q e. RR+'), frp], 'rpdivcld', '( Q / f ) e. RR+')
    L = '( log ` ( Q / f ) )'
    PHF = '( ( phi ` f ) / f )'
    CF = '( f / ( phi ` f ) )'
    LHS = '( %s x. %s )' % (PHF, L)
    ST = 'sum_ v e. %s ( 1 / ( phi ` v ) )' % TSQ
    SR = 'sum_ v e. %s ( 1 / ( phi ` v ) )' % RFQ
    STr = 'sum_ r e. %s ( 1 / ( phi ` r ) )' % TSQ
    sp0 = st([fnn, qfre, q1, w.inst('sumphiinv')], 'syl3anc', '%s <_ %s' % (LHS, STr))
    cbt = w.s([w.s([w.s([], 'fveq2', '( r = v -> ( phi ` r ) = ( phi ` v ) )')], 'oveq2d',
                   '( r = v -> ( 1 / ( phi ` r ) ) = ( 1 / ( phi ` v ) ) )')], 'cbvsumv', '%s = %s' % (STr, ST))
    sp = st([sp0, st([cbt], 'a1i', '%s = %s' % (STr, ST))], 'breqtrd', '%s <_ %s' % (LHS, ST))
    ss = st([qre, ffz, w.inst('lswinset')], 'syl2anc', '%s C_ %s' % (TSQ, RFQ))
    rffin = st([st([], 'fzfid', '%s e. Fin' % Q0S), a1(w, AW3, 'ssrab2', '%s C_ %s' % (RFQ, Q0S))], 'ssfid', '%s e. Fin' % RFQ)
    FZq = '( 1 ... %s )' % QF
    tsfin = st([st([], 'fzfid', '%s e. Fin' % FZq), a1(w, AW3, 'ssrab2', '%s C_ %s' % (TSQ, FZq))], 'ssfid', '%s e. Fin' % TSQ)
    # facts at r in RF
    AR = '( %s /\\ v e. %s )' % (AW3, RFQ)
    sr = mk(w, AR)
    rc = elrabst(w, AR, sr([], 'simpr', 'v e. %s' % RFQ), 'r', 'v', Q0S, rfc('r'), rfc('v'), rfceq(w, 'r', 'v'))
    rnn = sr([sr([rc], 'simpld', 'v e. %s' % Q0S), w.inst('elfznn')], 'syl', 'v e. NN')
    rgf = sr([sr([sr([rc], 'simprd', rfc('v'))], 'simprd', tc('v'))], 'simprd', '( v gcd f ) = 1')
    phr = sr([rnn], 'phicld', '( phi ` v ) e. NN')
    trp = sr([sr([phr], 'nnrpd', '( phi ` v ) e. RR+')], 'rpreccld', '( 1 / ( phi ` v ) ) e. RR+')
    tre = sr([trp], 'rpred', '( 1 / ( phi ` v ) ) e. RR')
    tge = sr([trp], 'rpge0d', '0 <_ ( 1 / ( phi ` v ) )')
    tcc = sr([tre], 'recnd', '( 1 / ( phi ` v ) ) e. CC')
    less = st([rffin, tre, tge, ss], 'fsumless', '%s <_ %s' % (ST, SR))
    # reals of the chain
    AT = '( %s /\\ v e. %s )' % (AW3, TSQ)
    stt = mk(w, AT)
    rtn = stt([elrabst(w, AT, stt([], 'simpr', 'v e. %s' % TSQ), 'r', 'v', FZq, tc('r'), tc('v'), tceq(w, 'r', 'v'))],
              'simpld', 'v e. %s' % FZq)
    ttre = stt([stt([stt([stt([stt([rtn, w.inst('elfznn')], 'syl', 'v e. NN')], 'phicld', '( phi ` v ) e. NN')], 'nnrpd',
                        '( phi ` v ) e. RR+')], 'rpreccld', '( 1 / ( phi ` v ) ) e. RR+')], 'rpred', '( 1 / ( phi ` v ) ) e. RR')
    phf = st([fnn], 'phicld', '( phi ` f ) e. NN')
    phfre = st([phf], 'nnred', '( phi ` f ) e. RR')
    phfc = st([phf], 'nncnd', '( phi ` f ) e. CC')
    phfne = st([phf], 'nnne0d', '( phi ` f ) =/= 0')
    phfk = st([st([phf], 'nnrpd', '( phi ` f ) e. RR+'), frp], 'rpdivcld', '%s e. RR+' % PHF)
    cfrp = st([frp, st([phf], 'nnrpd', '( phi ` f ) e. RR+')], 'rpdivcld', '%s e. RR+' % CF)
    cfre = st([cfrp], 'rpred', '%s e. RR' % CF)
    cfc = st([cfre], 'recnd', '%s e. CC' % CF)
    lre = st([qfrp], 'relogcld', '%s e. RR' % L)
    lhsre = st([st([phfk], 'rpred', '%s e. RR' % PHF), lre], 'remulcld', '%s e. RR' % LHS)
    stre = st([tsfin, ttre], 'fsumrecl', '%s e. RR' % ST)
    srre = st([rffin, tre], 'fsumrecl', '%s e. RR' % SR)
    lg = st([lhsre, stre, srre, sp, less], 'letrd', '%s <_ %s' % (LHS, SR))
    m1 = st([lhsre, srre, cfre, st([cfrp], 'rpge0d', '0 <_ %s' % CF), lg], 'lemul2ad',
            '( %s x. %s ) <_ ( %s x. %s )' % (CF, LHS, CF, SR))
    lc = st([lre], 'recnd', '%s e. CC' % L)
    as1 = st([cfc, st([st([phfk], 'rpred', '%s e. RR' % PHF)], 'recnd', '%s e. CC' % PHF), lc], 'mulassd',
             '( ( %s x. %s ) x. %s ) = ( %s x. %s )' % (CF, PHF, L, CF, LHS))
    c1 = st([fc, phfc, fne, phfne], 'divcan6d', '( %s x. %s ) = 1' % (CF, PHF))
    as2 = st([st([c1], 'oveq1d', '( ( %s x. %s ) x. %s ) = ( 1 x. %s )' % (CF, PHF, L, L)),
              st([lc], 'mullidd', '( 1 x. %s ) = %s' % (L, L))], 'eqtrd', '( ( %s x. %s ) x. %s ) = %s' % (CF, PHF, L, L))
    cl = st([as1, as2], 'eqtr3d', '( %s x. %s ) = %s' % (CF, LHS, L))
    m2 = st([cl, m1], 'eqbrtrrd', '%s <_ ( %s x. %s )' % (L, CF, SR))
    m3 = st([lre, st([cfre, srre], 'remulcld', '( %s x. %s ) e. RR' % (CF, SR)), bre, bge, m2], 'lemul1ad',
            '( %s x. B ) <_ ( ( %s x. %s ) x. B )' % (L, CF, SR))
    # the right-hand side as Lean's sum
    BODY1 = '( %s x. ( 1 / ( phi ` v ) ) )' % CF
    h1 = st([rffin, cfc, tcc], 'fsummulc2', '( %s x. %s ) = sum_ v e. %s %s' % (CF, SR, RFQ, BODY1))
    h2 = st([h1], 'oveq1d', '( ( %s x. %s ) x. B ) = ( sum_ v e. %s %s x. B )' % (CF, SR, RFQ, BODY1))
    b1c = sr([sr([cfc], 'adantr', '%s e. CC' % CF), tcc], 'mulcld', '%s e. CC' % BODY1)
    h3 = st([rffin, st([bre], 'recnd', 'B e. CC'), b1c], 'fsummulc1',
            '( sum_ v e. %s %s x. B ) = sum_ v e. %s ( %s x. B )' % (RFQ, BODY1, RFQ, BODY1))
    fcr = sr([fc], 'adantr', 'f e. CC')
    phfcr = sr([phfc], 'adantr', '( phi ` f ) e. CC')
    phrc = sr([phr], 'nncnd', '( phi ` v ) e. CC')
    d1 = sr([fcr, phfcr, sr([], '1cnd', '1 e. CC'), phrc, sr([phfne], 'adantr', '( phi ` f ) =/= 0'),
             sr([phr], 'nnne0d', '( phi ` v ) =/= 0')], 'divmuldivd',
            '%s = ( ( f x. 1 ) / ( ( phi ` f ) x. ( phi ` v ) ) )' % BODY1)
    pm = sr([rnn, sr([fnn], 'adantr', 'f e. NN'), rgf, w.inst('phimul')], 'syl3anc',
            '( phi ` ( v x. f ) ) = ( ( phi ` v ) x. ( phi ` f ) )')
    den = sr([sr([phfcr, phrc], 'mulcomd', '( ( phi ` f ) x. ( phi ` v ) ) = ( ( phi ` v ) x. ( phi ` f ) )'), pm],
             'eqtr4d', '( ( phi ` f ) x. ( phi ` v ) ) = ( phi ` ( v x. f ) )')
    d2 = sr([sr([fcr], 'mulridd', '( f x. 1 ) = f'), den], 'oveq12d',
            '( ( f x. 1 ) / ( ( phi ` f ) x. ( phi ` v ) ) ) = ( f / ( phi ` ( v x. f ) ) )')
    d3 = sr([sr([d1, d2], 'eqtrd', '%s = ( f / ( phi ` ( v x. f ) ) )' % BODY1)], 'oveq1d',
            '( %s x. B ) = ( ( f / ( phi ` ( v x. f ) ) ) x. B )' % BODY1)
    h4 = st([d3], 'sumeq2dv', 'sum_ v e. %s ( %s x. B ) = sum_ v e. %s ( ( f / ( phi ` ( v x. f ) ) ) x. B )' % (RFQ, BODY1, RFQ))
    rhs = st([st([h2, h3], 'eqtrd', '( ( %s x. %s ) x. B ) = sum_ v e. %s ( %s x. B )' % (CF, SR, RFQ, BODY1)), h4], 'eqtrd',
             '( ( %s x. %s ) x. B ) = sum_ v e. %s ( ( f / ( phi ` ( v x. f ) ) ) x. B )' % (CF, SR, RFQ))
    BV = '( ( f / ( phi ` ( v x. f ) ) ) x. B )'
    BR = '( ( f / ( phi ` ( r x. f ) ) ) x. B )'
    e1 = w.s([], 'oveq1', '( v = r -> ( v x. f ) = ( r x. f ) )')
    e2 = w.s([e1], 'fveq2d', '( v = r -> ( phi ` ( v x. f ) ) = ( phi ` ( r x. f ) ) )')
    e3 = w.s([e2], 'oveq2d', '( v = r -> ( f / ( phi ` ( v x. f ) ) ) = ( f / ( phi ` ( r x. f ) ) ) )')
    cbr = w.s([w.s([e3], 'oveq1d', '( v = r -> %s = %s )' % (BV, BR))], 'cbvsumv',
              'sum_ v e. %s %s = sum_ r e. %s %s' % (RFQ, BV, RFQ, BR))
    fin = st([m3, rhs], 'breqtrd', '( %s x. B ) <_ sum_ v e. %s %s' % (L, RFQ, BV))
    w.qed([fin, st([cbr], 'a1i', 'sum_ v e. %s %s = sum_ r e. %s %s' % (RFQ, BV, RFQ, BR))], 'breqtrd', S['lswinw'])
    return w


def lswsieve():
    from z4clib import HWIN, BLK, SW, WR
    from z4alib import HW, DIV
    w = W('lswsieve', 'The log-weighted primitive-character mean square over the window '
          '(Lean window_sieve): step 1 (lswinw), the regrouping (lswinreg), steps 2-5 (lswin).')
    AH = HWIN
    st = mk(w, AH)
    B = BLK('f')
    RFQ = RF(Q0)
    L = '( log ` ( Q / f ) )'
    LB = '( %s x. %s )' % (L, B)
    BV = '( ( f / ( phi ` ( v x. f ) ) ) x. %s )' % B
    BR = '( ( f / ( phi ` ( r x. f ) ) ) x. %s )' % B
    SR = 'sum_ r e. %s %s' % (RFQ, BR)
    SV = 'sum_ v e. %s %s' % (RFQ, BV)
    HWM = '( %s /\\ M e. ZZ )' % HW
    q2 = st([], 'simp1', '( Q e. RR /\\ 2 <_ Q )')
    qre = st([q2], 'simpld', 'Q e. RR')
    q2le = st([q2], 'simprd', '2 <_ Q')
    hw = st([st([], 'simp2', HWM)], 'simpld', HW)
    e3 = st([], 'simp3', '( E e. RR+ /\\ A. s e. %s A. m e. W ( m gcd s ) = 1 /\\ A. m e. W ( abs ` ( m - M ) ) <_ E )' % Q0S)
    erp = st([e3], 'simp1d', 'E e. RR+')
    qpos = st([st([], '0red', '0 e. RR'), a1(w, AH, '2re', '2 e. RR'), qre, a1(w, AH, '2pos', '0 < 2'), q2le],
              'ltletrd', '0 < Q')
    qrp = st([qre, qpos], 'elrpd', 'Q e. RR+')
    AF = '( %s /\\ f e. %s )' % (AH, Q0S)
    sf = mk(w, AF)
    ffz = sf([], 'simpr', 'f e. %s' % Q0S)
    fnn = sf([ffz, w.inst('elfznn')], 'syl', 'f e. NN')
    blk = sf([fnn, sf([hw], 'adantr', HW), w.inst('lsblkre')], 'syl2anc', '( %s e. RR /\\ 0 <_ %s )' % (B, B))
    blkre = sf([blk], 'simpld', '%s e. RR' % B)
    lw = sf([sf([q2], 'adantr', '( Q e. RR /\\ 2 <_ Q )'), ffz, blk, w.inst('lswinw')], 'syl3anc', '%s <_ %s' % (LB, SR))
    lre = sf([sf([sf([qrp], 'adantr', 'Q e. RR+'), sf([fnn], 'nnrpd', 'f e. RR+')], 'rpdivcld', '( Q / f ) e. RR+')],
             'relogcld', '%s e. RR' % L)
    lbre = sf([lre, blkre], 'remulcld', '%s e. RR' % LB)
    # the inner sum is real (through the letter v: fsumrecl carries $d k A and RF binds r)
    rffin = sf([sf([], 'fzfid', '%s e. Fin' % Q0S), a1(w, AF, 'ssrab2', '%s C_ %s' % (RFQ, Q0S))], 'ssfid', '%s e. Fin' % RFQ)
    AV = '( %s /\\ v e. %s )' % (AF, RFQ)
    sv = mk(w, AV)
    vc = elrabst(w, AV, sv([], 'simpr', 'v e. %s' % RFQ), 'r', 'v', Q0S, rfc('r'), rfc('v'), rfceq(w, 'r', 'v'))
    vnn = sv([sv([vc], 'simpld', 'v e. %s' % Q0S), w.inst('elfznn')], 'syl', 'v e. NN')
    fnnv = sv([fnn], 'adantr', 'f e. NN')
    phv = sv([sv([vnn, fnnv], 'nnmulcld', '( v x. f ) e. NN')], 'phicld', '( phi ` ( v x. f ) ) e. NN')
    bvre = sv([sv([sv([fnnv], 'nnred', 'f e. RR'), sv([phv], 'nnred', '( phi ` ( v x. f ) ) e. RR'),
                   sv([phv], 'nnne0d', '( phi ` ( v x. f ) ) =/= 0')], 'redivcld', '( f / ( phi ` ( v x. f ) ) ) e. RR'),
               sv([blkre], 'adantr', '%s e. RR' % B)], 'remulcld', '%s e. RR' % BV)
    svre = sf([rffin, bvre], 'fsumrecl', '%s e. RR' % SV)
    e1 = w.s([], 'oveq1', '( v = r -> ( v x. f ) = ( r x. f ) )')
    e2 = w.s([e1], 'fveq2d', '( v = r -> ( phi ` ( v x. f ) ) = ( phi ` ( r x. f ) ) )')
    e3b = w.s([e2], 'oveq2d', '( v = r -> ( f / ( phi ` ( v x. f ) ) ) = ( f / ( phi ` ( r x. f ) ) ) )')
    cbr = w.s([w.s([e3b], 'oveq1d', '( v = r -> %s = %s )' % (BV, BR))], 'cbvsumv', '%s = %s' % (SV, SR))
    srre = sf([sf([cbr], 'a1i', '%s = %s' % (SV, SR)), svre], 'eqeltrrd', '%s e. RR' % SR)
    fzfin = st([], 'fzfid', '%s e. Fin' % Q0S)
    X = 'sum_ f e. %s %s' % (Q0S, LB)
    Y = 'sum_ f e. %s %s' % (Q0S, SR)
    Z = 'sum_ q e. %s sum_ f e. %s ( ( f / ( phi ` q ) ) x. %s )' % (Q0S, DIV('q'), B)
    RHS = '( ( ( Q ^ 2 ) + %s ) x. %s )' % (WR(), SW('A'))
    le = st([fzfin, lbre, srre, lw], 'fsumle', '%s <_ %s' % (X, Y))
    hn = st([qre, st([st([], '0red', '0 e. RR'), qre, qpos], 'ltled', '0 <_ Q'), w.inst('flge0nn0')], 'syl2anc',
            '%s e. NN0' % Q0)
    AN = '( %s /\\ f e. NN )' % AH
    sn = mk(w, AN)
    hb = sn([sn([sn([sn([], 'simpr', 'f e. NN'), sn([hw], 'adantr', HW), w.inst('lsblkre')], 'syl2anc',
                    '( %s e. RR /\\ 0 <_ %s )' % (B, B))], 'simpld', '%s e. RR' % B)], 'recnd', '%s e. CC' % B)
    reg = w.s([hn, hb], 'lswinreg', '( %s -> %s = %s )' % (AH, Y, Z))
    lsw = w.s([], 'lswin', '( %s -> %s <_ %s )' % (AH, Z, RHS))
    ylew = st([reg, lsw], 'eqbrtrd', '%s <_ %s' % (Y, RHS))
    xre = st([fzfin, lbre], 'fsumrecl', '%s e. RR' % X)
    yre = st([fzfin, srre], 'fsumrecl', '%s e. RR' % Y)
    wr = st([st([a1(w, AH, '4re', '4 e. RR'), a1(w, AH, 'pire', '_pi e. RR')], 'remulcld', '( 4 x. _pi ) e. RR'),
             st([erp], 'rpred', 'E e. RR')], 'remulcld', '%s e. RR' % WR())
    AWn = '( %s /\\ n e. W )' % AH
    sn2 = mk(w, AWn)
    an = sn2([sn2([st([hw], 'simp3d', 'A : W --> CC')], 'adantr', 'A : W --> CC'), sn2([], 'simpr', 'n e. W')],
             'ffvelcdmd', '( A ` n ) e. CC')
    swre = st([st([hw], 'simp1d', 'W e. Fin'), sn2([sn2([an], 'abscld', '( abs ` ( A ` n ) ) e. RR')], 'resqcld',
                                                   '( ( abs ` ( A ` n ) ) ^ 2 ) e. RR')], 'fsumrecl', '%s e. RR' % SW('A'))
    rre = st([st([st([qre], 'resqcld', '( Q ^ 2 ) e. RR'), wr], 'readdcld', '( ( Q ^ 2 ) + %s ) e. RR' % WR()), swre],
             'remulcld', '%s e. RR' % RHS)
    w.qed([xre, yre, rre, le, ylew], 'letrd', S['lswsieve'])
    return w


ALL = {'lswinset': lswinset, 'lswinw': lswinw, 'lswsieve': lswsieve}

if __name__ == '__main__':
    for n in (sys.argv[1:] or list(ALL)):
        ALL[n]().run()
