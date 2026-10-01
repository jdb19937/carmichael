"""Sortie v3: the elementary shared layer.

phipfprod  ( M e. NN -> prod_ p e. PF( M ) ( 1 - ( 1 / p ) ) = ( ( phi ` M ) / M ) )
sqf2omle   ( ( D e. NN /\\ ( mmu ` D ) =/= 0 ) -> ( 2 ^ OM( D ) ) <_ D )
sqf3omle   ( ( D e. NN /\\ ( mmu ` D ) =/= 0 ) -> ( 3 ^ OM( D ) ) <_ ( D ^ 2 ) )
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm import W
from v3_lib import mkst
from cl import lift


def PFQ(X):
    return '{ q e. Prime | q || %s } ' % X


PFM = '{ q e. Prime | q || M }'
PFD = '{ q e. Prime | q || D }'
OMD = '( # ` %s )' % PFD


def prmfacts(w, ante, p):
    """closures for a prime p under ante"""
    f = mkst(w, ante)
    pp = f([f([], 'simpr', '%s e. %s' % (p, PFM if 'M' in ante else PFD)), w.inst('elrabi')],
           'syl', '%s e. Prime' % p)
    return pp


def phipfprod():
    w = W('phipfprod', 'Euler product for phi ( M ) / M over the prime divisors of M.')
    A = 'M e. NN'
    st = mkst(w, A)
    AP = '( M e. NN /\\ p e. %s )' % PFM
    sp = mkst(w, AP)
    pprm = sp([sp([], 'simpr', 'p e. %s' % PFM), w.inst('elrabi')], 'syl', 'p e. Prime')
    pnn = sp([pprm, w.inst('prmnn')], 'syl', 'p e. NN')
    prp = sp([pnn], 'nnrpd', 'p e. RR+')
    pc = sp([pnn], 'nncnd', 'p e. CC')
    pne = sp([prp], 'rpne0d', 'p =/= 0')
    onec = sp([sp([], '1red', '1 e. RR')], 'recnd', '1 e. CC')
    ds = sp([pc, onec, pc, pne], 'divsubdird',
            '( ( p - 1 ) / p ) = ( ( p / p ) - ( 1 / p ) )')
    di = sp([pc, pne], 'dividd', '( p / p ) = 1')
    d2 = sp([di], 'oveq1d', '( ( p / p ) - ( 1 / p ) ) = ( 1 - ( 1 / p ) )')
    fe = sp([ds, d2], 'eqtrd', '( ( p - 1 ) / p ) = ( 1 - ( 1 / p ) )')
    pe = st([fe], 'prodeq2dv',
            'prod_ p e. %s ( ( p - 1 ) / p ) = prod_ p e. %s ( 1 - ( 1 / p ) )' % (PFM, PFM))
    pr = w.s([], 'phiradlem',
             '( M e. NN -> ( ( phi ` M ) / M ) = prod_ p e. %s ( ( p - 1 ) / p ) )' % PFM)
    tr = st([pr, pe], 'eqtrd', '( ( phi ` M ) / M ) = prod_ p e. %s ( 1 - ( 1 / p ) )' % PFM)
    w.qed([tr], 'eqcomd',
          '( M e. NN -> prod_ p e. %s ( 1 - ( 1 / p ) ) = ( ( phi ` M ) / M ) )' % PFM)
    return w


def _sqfsetup(w, A):
    st = mkst(w, A)
    dnn = st([], 'simpl', 'D e. NN')
    dsqf = st([], 'simpr', '( mmu ` D ) =/= 0')
    sbq = w.s([], 'breq1', '( p = q -> ( p || D <-> q || D ) )')
    cb = w.s([sbq], 'cbvrabv', '{ p e. Prime | p || D } = %s' % PFD)
    cbd = st([cb], 'a1i', '{ p e. Prime | p || D } = %s' % PFD)
    fin0 = st([dnn, w.inst('prmdvdsfi')], 'syl', '{ p e. Prime | p || D } e. Fin')
    fin = st([cbd, fin0], 'eqeltrrd', '%s e. Fin' % PFD)
    pid = st([dnn, dsqf, w.inst('sqfprodid')], 'syl2anc', 'prod_ p e. %s p = D' % PFD)
    nf = w.s([], 'nfv', 'F/ p %s' % A)
    AP = '( %s /\\ p e. %s )' % (A, PFD)
    sp = mkst(w, AP)
    pprm = sp([sp([], 'simpr', 'p e. %s' % PFD), w.inst('elrabi')], 'syl', 'p e. Prime')
    pnn = sp([pprm, w.inst('prmnn')], 'syl', 'p e. NN')
    pre = sp([pnn], 'nnred', 'p e. RR')
    p2 = sp([sp([pprm, w.inst('prmuz2')], 'syl', 'p e. ( ZZ>= ` 2 )'), w.inst('eluz2gt1')],
            'syl', '1 < p')
    return dict(st=st, dnn=dnn, dsqf=dsqf, fin=fin, pid=pid, nf=nf, AP=AP, sp=sp,
                pprm=pprm, pnn=pnn, pre=pre)


def sqf2omle():
    w = W('sqf2omle', '2 to the number of prime divisors of a squarefree D is at most D.')
    A = '( D e. NN /\\ ( mmu ` D ) =/= 0 )'
    d = _sqfsetup(w, A)
    st, sp, AP = d['st'], d['sp'], d['AP']
    two = sp([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR')
    tw0 = sp([w.s([], '0le2', '0 <_ 2')], 'a1i', '0 <_ 2')
    ple = sp([sp([d['pprm'], w.inst('prmuz2')], 'syl', 'p e. ( ZZ>= ` 2 )'),
              w.inst('eluzle')], 'syl', '2 <_ p')
    le = st([d['nf'], d['fin'], two, tw0, d['pre'], ple], 'fprodle',
            'prod_ p e. %s 2 <_ prod_ p e. %s p' % (PFD, PFD))
    twoc = st([w.s([], '2cn', '2 e. CC')], 'a1i', '2 e. CC')
    cst = st([d['fin'], twoc, w.inst('fprodconst')], 'syl2anc',
             'prod_ p e. %s 2 = ( 2 ^ %s )' % (PFD, OMD))
    le2 = st([cst, le], 'eqbrtrrd', '( 2 ^ %s ) <_ prod_ p e. %s p' % (OMD, PFD))
    w.qed([le2, d['pid']], 'breqtrd', '( %s -> ( 2 ^ %s ) <_ D )' % (A, OMD))
    return w


def sqf3omle():
    w = W('sqf3omle', '3 to the number of prime divisors of a squarefree D is at most D squared.')
    A = '( D e. NN /\\ ( mmu ` D ) =/= 0 )'
    d = _sqfsetup(w, A)
    st, sp, AP = d['st'], d['sp'], d['AP']
    three = sp([w.s([], '3re', '3 e. RR')], 'a1i', '3 e. RR')
    th0 = sp([sp([], '0red', '0 e. RR'), three,
              sp([w.s([], '3pos', '0 < 3')], 'a1i', '0 < 3')], 'ltled', '0 <_ 3')
    pre = d['pre']
    psq = sp([pre, pre], 'remulcld', '( p x. p ) e. RR')
    ple = sp([sp([d['pprm'], w.inst('prmuz2')], 'syl', 'p e. ( ZZ>= ` 2 )'),
              w.inst('eluzle')], 'syl', '2 <_ p')
    from lin import nlinarith
    g = nlinarith(w, AP, [ple], '3 <_ ( p x. p )', leaves={'p': pre})
    le = st([d['nf'], d['fin'], three, th0, psq, g], 'fprodle',
            'prod_ p e. %s 3 <_ prod_ p e. %s ( p x. p )' % (PFD, PFD))
    threec = st([w.s([], '3cn', '3 e. CC')], 'a1i', '3 e. CC')
    cst = st([d['fin'], threec, w.inst('fprodconst')], 'syl2anc',
             'prod_ p e. %s 3 = ( 3 ^ %s )' % (PFD, OMD))
    # prod ( p x. p ) = ( prod p ) x. ( prod p ) = D ^ 2
    pcc = sp([d['pnn']], 'nncnd', 'p e. CC')
    pe2 = st([d['fin'], pcc, pcc], 'fprodmul',
             'prod_ p e. %s ( p x. p ) = ( prod_ p e. %s p x. prod_ p e. %s p )'
             % (PFD, PFD, PFD))
    dc = st([d['dnn']], 'nncnd', 'D e. CC')
    dsq = st([dc], 'sqvald', '( D ^ 2 ) = ( D x. D )')
    m1 = st([d['pid']], 'oveq1d',
            '( prod_ p e. %s p x. prod_ p e. %s p ) = ( D x. prod_ p e. %s p )' % (PFD, PFD, PFD))
    m2 = st([d['pid']], 'oveq2d',
            '( D x. prod_ p e. %s p ) = ( D x. D )' % PFD)
    m3 = st([m1, m2], 'eqtrd',
            '( prod_ p e. %s p x. prod_ p e. %s p ) = ( D x. D )' % (PFD, PFD))
    m4 = st([pe2, m3], 'eqtrd', 'prod_ p e. %s ( p x. p ) = ( D x. D )' % PFD)
    m5 = st([m4, dsq], 'eqtr4d', 'prod_ p e. %s ( p x. p ) = ( D ^ 2 )' % PFD)
    le2 = st([cst, le], 'eqbrtrrd', '( 3 ^ %s ) <_ prod_ p e. %s ( p x. p )' % (OMD, PFD))
    w.qed([le2, m5], 'breqtrd', '( %s -> ( 3 ^ %s ) <_ ( D ^ 2 ) )' % (A, OMD))
    return w


ALL = {'phipfprod': phipfprod, 'sqf2omle': sqf2omle, 'sqf3omle': sqf3omle}

if __name__ == '__main__':
    names = sys.argv[1:] or list(ALL)
    for n in names:
        ALL[n]().run()
