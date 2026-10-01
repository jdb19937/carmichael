"""Sortie CEN1: Re ( -L'/L ) from the Landau expansion on the 13/8 square (cenlnd), adapted from KD1's kdl2."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from cen1lib import *
from cl import split_imp
from c9lib import top_and
from c8lib import tsub
from lin import linarith

only = sys.argv[1:]
A13 = '( %s - ( %s + ( _i x. %s ) ) )' % (CT('T'), R138, R138)
B13 = '( %s + ( %s + ( _i x. %s ) ) )' % (CT('T'), R138, R138)


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


def gen_lnd():
    w = W('cenlnd', 'The Landau expansion in real parts: on ` Re S > 1 ` inside the ` 3 / 2 ` disc about ` 2 + i T ` , ` Re ( -L\'/L ) ( S ) <_ 17500000 log ( N ( abs T + 2 ) ) - sum_ZD Re ( m_q / ( S - q ) ) ` , every term ` >_ 0 ` (the core of Lean Census ` re_neg_logDeriv_le ` , ` re_neg_logDeriv_le_of_zero ` ; C10 ~ lndlchrk , KD1 ~ kdlogdv , ~ kdre1 ).')
    A0, C0 = split_imp(S['cenlnd'])
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    X1, X2 = top_and(A0)
    x1 = s([], 'simpl', X1); x2 = s([], 'simpr', X2)
    chi = s([x1], 'simpld', CHI); tr = s([x1], 'simprd', 'T e. RR')
    SS = 'S'
    s0c = s([x2], 'simp1d', 'S e. CC'); d32 = s([x2], 'simp2d', '( abs ` ( S - %s ) ) <_ ( 3 / 2 )' % CT('T')); s01 = s([x2], 'simp3d', '1 < ( Re ` S )')
    rsr = s([s0c], 'recld', '( Re ` S ) e. RR')
    cs = Closure(w, A0, {'( Re ` S )': ('RR', rsr)}); cs.atom('( Re ` S )')
    s00 = linarith(w, A0, [s01], '0 < ( Re ` S )', closure=cs)
    shp = s([s([s0c, s00], 'jca', '( S e. CC /\\ 0 < ( Re ` S ) )'), s([w.s([], '0red', '( %s -> 0 e. RR )' % A0), w.inst('elhp2')], 'syl', '( S e. %s <-> ( S e. CC /\\ 0 < ( Re ` S ) ) )' % HP0)],
            'mpbird', 'S e. %s' % HP0)
    DDs = stmt('ef2ddl').split(' -> ', 1)[1][:-2]
    dd = s([chi, w.inst('ef2ddl')], 'syl', DDs)
    NV = top_and(top_and(DDs)[2])[1]
    nv = s([s([dd], 'simp3d', top_and(DDs)[2])], 'simprd', NV)
    idw = w.s([], 'id', '( w = S -> w = S )')
    cw, nw = w.wcongr('( 1 < ( Re ` w ) -> ( %s ` w ) =/= 0 )' % LFN, {'w': SS}, 'w = S', {'w': idw})
    lnz = s([s([shp, nv, w.s([cw], 'rspcv', '( S e. %s -> ( %s -> %s ) )' % (HP0, NV, nw))], 'sylc', nw), s01], 'mpd', '( %s ` S ) =/= 0' % LFN)
    LN = stmt('lndlchrk')
    lna, lnc = split_imp(LN)
    ln = s([s([chi, tr], 'jca', top_and(lna)[0]), s([s0c, d32, lnz], '3jca', top_and(lna)[1]), w.inst('lndlchrk')], 'syl2anc', lnc)
    SG = 'sum_ q e. %s ( %s / ( S - q ) )' % (ZD(), MU())
    LD = lnc.split('( abs ` ( ', 1)[1].rsplit(' - %s ) ) <_ ' % SG, 1)[0]
    assert lnc == '( abs ` ( %s - %s ) ) <_ %s' % (LD, SG, KL()), lnc[-300:]
    KD = stmt('kdlogdv'); kda, kdc = split_imp(KD)
    assert kdc == '%s = -u %s' % (LD, LAM('S')), kdc[-200:]
    ldeq = s([chi, s([s0c, s01], 'jca', top_and(kda)[1]), w.inst('kdlogdv')], 'syl2anc', kdc)
    lamc = None
    # zeros
    LZ = stmt('lchrzc8'); lza, lzc = split_imp(LZ)
    lz = s([s([chi, tr], 'jca', lza), w.inst('lchrzc8')], 'syl', lzc)
    zfin = s([lz], 'simp1d', top_and(lzc)[0]); zord = s([lz], 'simp2d', top_and(lzc)[1])
    Aq = '( %s /\\ q e. %s )' % (A0, ZD())
    a = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Aq, f))
    L = lambda st: lift(w, st, Aq)
    qq = a([], 'simpr', 'q e. %s' % ZD())
    M_ = MU('q')
    mn = a([qq, a([L(zord), w.inst('rsp')], 'syl', '( q e. %s -> %s e. NN )' % (ZD(), M_))], 'mpd', '%s e. NN' % M_)
    mr = a([mn], 'nnred', '%s e. RR' % M_); m0 = a([a([mn], 'nnrpd', '%s e. RR+' % M_)], 'rpge0d', '0 <_ %s' % M_); mc = a([mr], 'recnd', '%s e. CC' % M_)
    rq = a([L(chi), L(tr), qq, w.inst('kdre1')], 'syl3anc', '( Re ` q ) <_ 1')
    SQ13 = SQ(CT('T'), R138)
    cq = Closure(w, Aq, {'T': ('RR', L(tr))})
    cct = a([w.s([w.s([], '2cn', '2 e. CC')], 'a1i', '( %s -> 2 e. CC )' % Aq), a([w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % Aq), a([L(tr)], 'recnd', 'T e. CC')], 'mulcld', '( _i x. T ) e. CC')],
            'addcld', '%s e. CC' % CT('T'))
    RI_ = '( %s + ( _i x. %s ) )' % (R138, R138)
    ric = a([a([cq.mem(R138, 'RR')], 'recnd', '%s e. CC' % R138), a([w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % Aq), a([cq.mem(R138, 'RR')], 'recnd', '%s e. CC' % R138)], 'mulcld', '( _i x. %s ) e. CC' % R138)],
            'addcld', '%s e. CC' % RI_)
    sqcc = a([a([a([cct, ric], 'subcld', '%s e. CC' % A13), a([cct, ric], 'addcld', '%s e. CC' % B13)], 'jca', '( %s e. CC /\\ %s e. CC )' % (A13, B13)), w.inst('crectss')], 'syl', '%s C_ CC' % SQ13)
    qc = a([sqcc, a([w.s([w.s([], 'ssrab2', '%s C_ %s' % (ZD(), SQ13))], 'a1i', '( %s -> %s C_ %s )' % (Aq, ZD(), SQ13)), qq], 'sseldd', 'q e. %s' % SQ13)], 'sseldd', 'q e. CC')
    Z_ = '( S - q )'
    zc = a([L(s0c), qc], 'subcld', '%s e. CC' % Z_)
    rz = a([L(s0c), qc], 'resubd', '( Re ` %s ) = ( ( Re ` S ) - ( Re ` q ) )' % Z_)
    cq.leaf('( Re ` q )', 'RR', a([qc], 'recld', '( Re ` q ) e. RR')); cq.atom('( Re ` q )')
    cq.leaf('( Re ` S )', 'RR', L(rsr)); cq.atom('( Re ` S )')
    cq.leaf('( Re ` %s )' % Z_, 'RR', a([zc], 'recld', '( Re ` %s ) e. RR' % Z_)); cq.atom('( Re ` %s )' % Z_)
    zpos = linarith(w, Aq, [rz, L(s01), rq], '0 < ( Re ` %s )' % Z_, closure=cq)
    tnn = a([a([mr, m0], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (M_, M_)), a([zc, zpos], 'jca', '( %s e. CC /\\ 0 < ( Re ` %s ) )' % (Z_, Z_)), w.inst('redivnn')], 'syl2anc', '0 <_ %s' % RQ('S'))
    # zero off the zero set: S - q =/= 0
    rne0 = a([a([zpos], 'gt0ne0d', '( Re ` %s ) =/= 0' % Z_), w.s([w.s([], 're0', '( Re ` 0 ) = 0')], 'a1i', '( %s -> ( Re ` 0 ) = 0 )' % Aq)], 'neeqtrrd', '( Re ` %s ) =/= ( Re ` 0 )' % Z_)
    zn = a([rne0, w.s([w.s([], 'fveq2', '( %s = 0 -> ( Re ` %s ) = ( Re ` 0 ) )' % (Z_, Z_))], 'necon3i', '( ( Re ` %s ) =/= ( Re ` 0 ) -> %s =/= 0 )' % (Z_, Z_))], 'syl', '%s =/= 0' % Z_)
    mzc = a([mc, zc, zn], 'divcld', '( %s / %s ) e. CC' % (M_, Z_))
    alln = s([a([a([mzc], 'recld', '%s e. RR' % RQ('S')), tnn], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (RQ('S'), RQ('S')))], 'ralrimiva', 'A. q e. %s ( %s e. RR /\\ 0 <_ %s )' % (ZD(), RQ('S'), RQ('S')))
    SRe = 'sum_ q e. %s %s' % (ZD(), RQ('S'))
    f3 = s([zfin, mzc], 'fsumre', '( Re ` %s ) = %s' % (SG, SRe))
    sre = s([zfin, a([mzc], 'recld', '%s e. RR' % RQ('S'))], 'fsumrecl', '%s e. RR' % SRe)
    # the real-part chain
    sgc = s([zfin, mzc], 'fsumcl', '%s e. CC' % SG)
    hol = s([dd], 'simp1d', top_and(DDs)[0])
    ldn = s([s([hol, w.inst('holf')], 'syl', '( CC _D %s ) : %s --> CC' % (LFN, HP0)), shp], 'ffvelcdmd', '( ( CC _D %s ) ` S ) e. CC' % LFN)
    lfv = s([s([s([hol, w.inst('simpl')], 'syl', '%s e. ( %s -cn-> CC )' % (LFN, HP0)), w.inst('cncff')], 'syl', '%s : %s --> CC' % (LFN, HP0)), shp], 'ffvelcdmd', '( %s ` S ) e. CC' % LFN)
    ldc = s([ldn, lfv, lnz], 'divcld', '%s e. CC' % LD)
    lmc = s([s([ldeq, ldc], 'eqeltrrd', '-u %s e. CC' % LAM('S'))], 'negcld', '-u -u %s e. CC' % LAM('S')) if False else None
    DIF = '( %s - %s )' % (LD, SG)
    difc = s([ldc, sgc], 'subcld', '%s e. CC' % DIF)
    rdf = s([ldc, sgc], 'resubd', '( Re ` %s ) = ( ( Re ` %s ) - ( Re ` %s ) )' % (DIF, LD, SG))
    rn = s([difc], 'renegd', '( Re ` -u %s ) = -u ( Re ` %s )' % (DIF, DIF))
    rnl = s([s([difc], 'negcld', '-u %s e. CC' % DIF)], 'releabsd', '( Re ` -u %s ) <_ ( abs ` -u %s )' % (DIF, DIF))
    an = s([difc], 'absnegd', '( abs ` -u %s ) = ( abs ` %s )' % (DIF, DIF))
    # LAM e. CC (lchvmcvg + isumcl)
    NL = '-u %s' % LAM('S')
    A1 = '( %s /\\ k e. NN )' % A0
    b = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A1, f))
    kn = b([], 'simpr', 'k e. NN')
    TK = '( ( %s x. ( Lam ` k ) ) x. ( k ^c -u S ) )' % CHV('k')
    nx1 = s([chi], 'simpld', NXH)
    tkc = b([b([b([lift(w, nx1, A1), kn], 'jca', '( %s /\\ k e. NN )' % NXH), w.inst('lchrcl')], 'syl', '%s e. CC' % CHV('k')),
             b([b([kn, w.inst('vmacl')], 'syl', '( Lam ` k ) e. RR')], 'recnd', '( Lam ` k ) e. CC')], 'mulcld', '( %s x. ( Lam ` k ) ) e. CC' % CHV('k'))
    tkc = b([tkc, b([b([kn], 'nncnd', 'k e. CC'), b([lift(w, s0c, A1)], 'negcld', '-u S e. CC')], 'cxpcld', '( k ^c -u S ) e. CC')], 'mulcld', '%s e. CC' % TK)
    from congr import mptval
    NB = '( ( %s x. ( Lam ` n ) ) x. ( n ^c -u S ) )' % CHV('n')
    fv, val = mptval(w, A1, 'n', 'NN', NB, 'k', kn, exs=b([tkc], 'elexd', '%s e. _V' % TK), gen=w.g)
    assert val == TK, val
    cvL = tsub(stmt('lchvmcvg'), {'Z': 'S'})
    cva, cvc = split_imp(cvL)
    cv = s([nx1, s([s0c, s01], 'jca', '( S e. CC /\\ 1 < ( Re ` S ) )'), w.inst('lchvmcvg')], 'syl2anc', cvc)
    lamc = s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), s([], '1zzd', '1 e. ZZ'), fv, tkc, cv], 'isumcl', '%s e. CC' % LAM('S'))
    rld = s([s([ldeq], 'fveq2d', '( Re ` %s ) = ( Re ` %s )' % (LD, NL)), s([lamc], 'renegd', '( Re ` %s ) = -u ( Re ` %s )' % (NL, LAM('S')))], 'eqtrd', '( Re ` %s ) = -u ( Re ` %s )' % (LD, LAM('S')))
    cz = Closure(w, A0, {})
    for e_, st in (('( Re ` %s )' % LD, s([ldc], 'recld', '( Re ` %s ) e. RR' % LD)), ('( Re ` %s )' % SG, s([sgc], 'recld', '( Re ` %s ) e. RR' % SG)),
                   ('( Re ` %s )' % DIF, s([difc], 'recld', '( Re ` %s ) e. RR' % DIF)), ('( Re ` -u %s )' % DIF, s([s([difc], 'negcld', '-u %s e. CC' % DIF)], 'recld', '( Re ` -u %s ) e. RR' % DIF)),
                   ('( abs ` %s )' % DIF, s([difc], 'abscld', '( abs ` %s ) e. RR' % DIF)),
                   ('( abs ` -u %s )' % DIF, s([s([difc], 'negcld', '-u %s e. CC' % DIF)], 'abscld', '( abs ` -u %s ) e. RR' % DIF)),
                   ('( Re ` %s )' % LAM('S'), s([lamc], 'recld', '( Re ` %s ) e. RR' % LAM('S'))), (SRe, sre)):
        cz.leaf(e_, 'RR', st); cz.atom(e_)
    nn_ = s([nx1], 'simpld', 'N e. NN')
    at = s([s([tr], 'recnd', 'T e. CC')], 'abscld', '( abs ` T ) e. RR')
    ca = Closure(w, A0, {'( abs ` T )': ('RR', at)}); ca.atom('( abs ` T )')
    t2p = s([ca.mem('( ( abs ` T ) + 2 )', 'RR'), linarith(w, A0, [s([s([tr], 'recnd', 'T e. CC')], 'absge0d', '0 <_ ( abs ` T )')], '0 < ( ( abs ` T ) + 2 )', closure=ca)], 'elrpd', '( ( abs ` T ) + 2 ) e. RR+')
    XT = '( N x. ( ( abs ` T ) + 2 ) )'
    lg = s([s([s([nn_], 'nnrpd', 'N e. RR+'), t2p], 'rpmulcld', '%s e. RR+' % XT)], 'relogcld', '( log ` %s ) e. RR' % XT)
    cz.leaf('( log ` %s )' % XT, 'RR', lg); cz.atom('( log ` %s )' % XT)
    bd = linarith(w, A0, [rld, rdf, rn, rnl, an, ln, f3], '( Re ` %s ) <_ ( %s - %s )' % (LAM('S'), KL(), SRe), closure=cz)
    w.qed([bd, alln], 'jca', S['cenlnd'])
    return run(w)


if __name__ == '__main__':
    gen_lnd()
