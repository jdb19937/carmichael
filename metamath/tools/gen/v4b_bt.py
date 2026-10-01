"""Sortie v4b block 8c: the two algebraic steps of the Brun-Titchmarsh assembly."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm import W
from v4b_lib import mkst
import num
from lin import linarith

C14 = num.nat_text(14)
C10 = num.nat_text(10)
K1 = '( 5 / %s )' % C14
K2 = '( %s / 5 )' % C14
Q = '( D / ( B x. C ) )'
MID = '( ( ( B / A ) x. ( %s x. C ) ) x. ( %s x. %s ) )' % (K1, K2, Q)
MANT = '( ( A e. RR+ /\\ B e. RR+ ) /\\ ( C e. RR+ /\\ D e. RR+ ) )'
EANT = '( %s /\\ ( ( %s x. B ) x. A ) <_ C )' % (MANT, C10)


def _rp(w, st):
    d = {}
    d['arp'] = st([], 'simpll', 'A e. RR+')
    d['brp'] = st([], 'simplr', 'B e. RR+')
    d['crp'] = st([], 'simprl', 'C e. RR+')
    d['drp'] = st([], 'simprr', 'D e. RR+')
    for k, v in (('a', 'A'), ('b', 'B'), ('c', 'C'), ('d', 'D')):
        d[k + 'cc'] = st([d[k + 'rp']], 'rpcnd', '%s e. CC' % v)
        d[k + 'ne'] = st([d[k + 'rp']], 'rpne0d', '%s =/= 0' % v)
        d[k + 're'] = st([d[k + 'rp']], 'rpred', '%s e. RR' % v)
        d[k + 'ge'] = st([d[k + 'rp'], w.inst('rpge0')], 'syl', '0 <_ %s' % v)
    return d


def mainid():
    w = W('mainid', 'The main-term identity of the Brun-Titchmarsh assembly.')
    st = mkst(w, MANT)
    d = _rp(w, st)
    ba = st([d['brp'], d['arp']], 'rpdivcld', '( B / A ) e. RR+')
    bacc = st([ba], 'rpcnd', '( B / A ) e. CC')
    bc = st([d['brp'], d['crp']], 'rpmulcld', '( B x. C ) e. RR+')
    bccc = st([bc], 'rpcnd', '( B x. C ) e. CC')
    bcne = st([bc], 'rpne0d', '( B x. C ) =/= 0')
    k1c = st([num.cc(w, K1)], 'a1i', '%s e. CC' % K1)
    k2c = st([num.cc(w, K2)], 'a1i', '%s e. CC' % K2)
    qcc = st([st([d['drp'], bc], 'rpdivcld', '%s e. RR+' % Q)], 'rpcnd', '%s e. CC' % Q)
    bacm = st([bacc, d['ccc']], 'mulcld', '( ( B / A ) x. C ) e. CC')
    s1 = st([bacc, k1c, d['ccc']], 'mul12d',
            '( ( B / A ) x. ( %s x. C ) ) = ( %s x. ( ( B / A ) x. C ) )' % (K1, K1))
    s2 = st([s1], 'oveq1d',
            '%s = ( ( %s x. ( ( B / A ) x. C ) ) x. ( %s x. %s ) )' % (MID, K1, K2, Q))
    s3 = st([k1c, bacm, k2c, qcc], 'mul4d',
            '( ( %s x. ( ( B / A ) x. C ) ) x. ( %s x. %s ) ) = '
            '( ( %s x. %s ) x. ( ( ( B / A ) x. C ) x. %s ) )' % (K1, K2, Q, K1, K2, Q))
    # ( 5 / 14 ) x. ( 14 / 5 ) = 1
    c5 = st([num.cc_nat(w, 5)], 'a1i', '5 e. CC')
    c5n = st([num.fact(w, '5', 'ne0')], 'a1i', '5 =/= 0')
    c14 = st([num.cc_nat(w, 14)], 'a1i', '%s e. CC' % C14)
    c14n = st([num.fact(w, C14, 'ne0')], 'a1i', '%s =/= 0' % C14)
    dmd = st([st([c5, c14], 'jca', '( 5 e. CC /\\ %s e. CC )' % C14),
              st([st([c14, c14n], 'jca', '( %s e. CC /\\ %s =/= 0 )' % (C14, C14)),
                  st([c5, c5n], 'jca', '( 5 e. CC /\\ 5 =/= 0 )')], 'jca',
                 '( ( %s e. CC /\\ %s =/= 0 ) /\\ ( 5 e. CC /\\ 5 =/= 0 ) )' % (C14, C14))],
             'jca',
             '( ( 5 e. CC /\\ %s e. CC ) /\\ ( ( %s e. CC /\\ %s =/= 0 ) /\\ ( 5 e. CC /\\ 5 =/= 0 ) ) )'
             % (C14, C14, C14))
    kk0 = st([dmd, w.inst('divmuldiv')], 'syl',
             '( %s x. %s ) = ( ( 5 x. %s ) / ( %s x. 5 ) )' % (K1, K2, C14, C14))
    c70 = num.nat_text(70)
    kk1 = st([st([st([num.mul_nat(w, 5, 14)], 'a1i', '( 5 x. %s ) = %s' % (C14, c70)),
                  st([num.mul_nat(w, 14, 5)], 'a1i', '( %s x. 5 ) = %s' % (C14, c70))],
                 'oveq12d', '( ( 5 x. %s ) / ( %s x. 5 ) ) = ( %s / %s )'
                 % (C14, C14, c70, c70)),
              st([st([num.cc_nat(w, 70)], 'a1i', '%s e. CC' % c70),
                  st([num.fact(w, c70, 'ne0')], 'a1i', '%s =/= 0' % c70)], 'dividd',
                 '( %s / %s ) = 1' % (c70, c70))], 'eqtrd',
             '( ( 5 x. %s ) / ( %s x. 5 ) ) = 1' % (C14, C14))
    kk = st([kk0, kk1], 'eqtrd', '( %s x. %s ) = 1' % (K1, K2))
    X = '( ( ( B / A ) x. C ) x. %s )' % Q
    s4 = st([st([kk], 'oveq1d', '( ( %s x. %s ) x. %s ) = ( 1 x. %s )' % (K1, K2, X, X)),
             st([st([bacm, qcc], 'mulcld', '%s e. CC' % X)], 'mullidd',
                '( 1 x. %s ) = %s' % (X, X))], 'eqtrd',
            '( ( %s x. %s ) x. %s ) = %s' % (K1, K2, X, X))
    s5 = st([st([d['bcc'], d['ccc'], st([d['acc'], d['ane']], 'jca',
                                        '( A e. CC /\\ A =/= 0 )'), w.inst('div23')],
                'syl3anc', '( ( B x. C ) / A ) = ( ( B / A ) x. C )')], 'eqcomd',
            '( ( B / A ) x. C ) = ( ( B x. C ) / A )')
    s6 = st([s5], 'oveq1d', '%s = ( ( ( B x. C ) / A ) x. %s )' % (X, Q))
    dmd2 = st([st([bccc, d['dcc']], 'jca', '( ( B x. C ) e. CC /\\ D e. CC )'),
               st([st([d['acc'], d['ane']], 'jca', '( A e. CC /\\ A =/= 0 )'),
                   st([bccc, bcne], 'jca', '( ( B x. C ) e. CC /\\ ( B x. C ) =/= 0 )')],
                  'jca',
                  '( ( A e. CC /\\ A =/= 0 ) /\\ ( ( B x. C ) e. CC /\\ ( B x. C ) =/= 0 ) )')],
              'jca',
              '( ( ( B x. C ) e. CC /\\ D e. CC ) /\\ ( ( A e. CC /\\ A =/= 0 ) /\\ ( ( B x. C ) e. CC /\\ ( B x. C ) =/= 0 ) ) )')
    s7 = st([dmd2, w.inst('divmuldiv')], 'syl',
            '( ( ( B x. C ) / A ) x. %s ) = ( ( ( B x. C ) x. D ) / ( A x. ( B x. C ) ) )' % Q)
    s8 = st([st([d['acc'], bccc], 'mulcomd', '( A x. ( B x. C ) ) = ( ( B x. C ) x. A )')],
            'oveq2d',
            '( ( ( B x. C ) x. D ) / ( A x. ( B x. C ) ) ) = '
            '( ( ( B x. C ) x. D ) / ( ( B x. C ) x. A ) )')
    s9 = st([d['dcc'], st([d['acc'], d['ane']], 'jca', '( A e. CC /\\ A =/= 0 )'),
             st([bccc, bcne], 'jca', '( ( B x. C ) e. CC /\\ ( B x. C ) =/= 0 )'),
             w.inst('divcan5')], 'syl3anc',
            '( ( ( B x. C ) x. D ) / ( ( B x. C ) x. A ) ) = ( D / A )')
    chain = st([st([s6, s7], 'eqtrd',
                   '%s = ( ( ( B x. C ) x. D ) / ( A x. ( B x. C ) ) )' % X),
                st([s8, s9], 'eqtrd',
                   '( ( ( B x. C ) x. D ) / ( A x. ( B x. C ) ) ) = ( D / A )')], 'eqtrd',
               '%s = ( D / A )' % X)
    w.qed([st([st([s2, s3], 'eqtrd',
                  '%s = ( ( %s x. %s ) x. %s )' % (MID, K1, K2, X)), s4], 'eqtrd',
               '%s = %s' % (MID, X)), chain], 'eqtrd',
          '( %s -> %s = ( D / A ) )' % (MANT, MID))
    return w


def errid():
    w = W('errid', 'The error-term bound of the Brun-Titchmarsh assembly.')
    st = mkst(w, EANT)
    s0 = st([], 'simpl', MANT)
    d = {}
    d['arp'] = st([s0], 'simplld', 'A e. RR+')
    d['brp'] = st([s0], 'simplrd', 'B e. RR+')
    d['crp'] = st([s0], 'simprld', 'C e. RR+')
    d['drp'] = st([s0], 'simprrd', 'D e. RR+')
    for k, v in (('a', 'A'), ('b', 'B'), ('c', 'C'), ('d', 'D')):
        d[k + 'cc'] = st([d[k + 'rp']], 'rpcnd', '%s e. CC' % v)
        d[k + 'ne'] = st([d[k + 'rp']], 'rpne0d', '%s =/= 0' % v)
        d[k + 're'] = st([d[k + 'rp']], 'rpred', '%s e. RR' % v)
        d[k + 'ge'] = st([d[k + 'rp'], w.inst('rpge0')], 'syl', '0 <_ %s' % v)
    hyp = st([], 'simpr', '( ( %s x. B ) x. A ) <_ C' % C10)
    c10re = st([num.re_nat(w, 10)], 'a1i', '%s e. RR' % C10)
    c10cc = st([num.cc_nat(w, 10)], 'a1i', '%s e. CC' % C10)
    tbre = st([c10re, d['bre']], 'remulcld', '( %s x. B ) e. RR' % C10)
    lhsre = st([tbre, d['are']], 'remulcld', '( ( %s x. B ) x. A ) e. RR' % C10)
    mul = st([lhsre, d['cre'], d['dre'], d['dge'], hyp], 'lemul2ad',
             '( D x. ( ( %s x. B ) x. A ) ) <_ ( D x. C )' % C10)
    dv = st([mul, d['brp']], 'lediv1dd',
            '( ( D x. ( ( %s x. B ) x. A ) ) / B ) <_ ( ( D x. C ) / B )' % C10)
    id1 = st([st([st([c10cc, d['bcc'], d['acc']], 'mul32d',
                     '( ( %s x. B ) x. A ) = ( ( %s x. A ) x. B )' % (C10, C10))], 'oveq2d',
                 '( D x. ( ( %s x. B ) x. A ) ) = ( D x. ( ( %s x. A ) x. B ) )' % (C10, C10)),
              st([st([d['dcc'], st([c10cc, d['acc']], 'mulcld', '( %s x. A ) e. CC' % C10),
                      d['bcc']], 'mulassd',
                     '( ( D x. ( %s x. A ) ) x. B ) = ( D x. ( ( %s x. A ) x. B ) )'
                     % (C10, C10))], 'eqcomd',
                 '( D x. ( ( %s x. A ) x. B ) ) = ( ( D x. ( %s x. A ) ) x. B )' % (C10, C10))],
             'eqtrd',
             '( D x. ( ( %s x. B ) x. A ) ) = ( ( D x. ( %s x. A ) ) x. B )' % (C10, C10))
    id2 = st([st([d['dcc'], st([c10cc, d['acc']], 'mulcld', '( %s x. A ) e. CC' % C10)],
                 'mulcld', '( D x. ( %s x. A ) ) e. CC' % C10), d['bcc'], d['bne'],
              w.inst('divcan4')], 'syl3anc',
             '( ( ( D x. ( %s x. A ) ) x. B ) / B ) = ( D x. ( %s x. A ) )' % (C10, C10))
    id3 = st([d['dcc'], c10cc, d['acc']], 'mul12d',
             '( D x. ( %s x. A ) ) = ( %s x. ( D x. A ) )' % (C10, C10))
    idq = st([st([st([id1], 'oveq1d',
                     '( ( D x. ( ( %s x. B ) x. A ) ) / B ) = ( ( ( D x. ( %s x. A ) ) x. B ) / B ) '
                     % (C10, C10)), id2], 'eqtrd',
                 '( ( D x. ( ( %s x. B ) x. A ) ) / B ) = ( D x. ( %s x. A ) )' % (C10, C10)),
              id3], 'eqtrd',
             '( ( D x. ( ( %s x. B ) x. A ) ) / B ) = ( %s x. ( D x. A ) )' % (C10, C10))
    f5 = '( 1 / 5 )'
    f5re = st([num.real(w, f5)], 'a1i', '%s e. RR' % f5)
    f5ge = st([num.fact(w, f5, 'ge0')], 'a1i', '0 <_ %s' % f5)
    f5cc = st([num.cc(w, f5)], 'a1i', '%s e. CC' % f5)
    dare = st([d['dre'], d['are']], 'remulcld', '( D x. A ) e. RR')
    lft = st([c10re, dare], 'remulcld', '( %s x. ( D x. A ) ) e. RR' % C10)
    rgt = st([st([d['dre'], d['cre']], 'remulcld', '( D x. C ) e. RR'), d['bre'], d['bne']],
             'redivcld', '( ( D x. C ) / B ) e. RR')
    mul2 = st([lft, rgt, f5re, f5ge, st([idq, dv], 'eqbrtrrd',
                                        '( %s x. ( D x. A ) ) <_ ( ( D x. C ) / B )' % C10)],
              'lemul2ad',
              '( %s x. ( %s x. ( D x. A ) ) ) <_ ( %s x. ( ( D x. C ) / B ) )'
              % (f5, C10, f5))
    kk = st([num.mul_lit(w, 10, f5)], 'a1i', '( %s x. %s ) = 2' % (C10, f5))
    kc = st([st([c10cc, f5cc], 'mulcomd', '( %s x. %s ) = ( %s x. %s )' % (C10, f5, f5, C10)),
             kk], 'eqtr3d', '( %s x. %s ) = 2' % (f5, C10))
    id4 = st([st([st([f5cc, c10cc, st([d['dcc'], d['acc']], 'mulcld', '( D x. A ) e. CC')],
                    'mulassd',
                    '( ( %s x. %s ) x. ( D x. A ) ) = ( %s x. ( %s x. ( D x. A ) ) )'
                    % (f5, C10, f5, C10))], 'eqcomd',
                 '( %s x. ( %s x. ( D x. A ) ) ) = ( ( %s x. %s ) x. ( D x. A ) )'
                 % (f5, C10, f5, C10)),
              st([kc], 'oveq1d',
                 '( ( %s x. %s ) x. ( D x. A ) ) = ( 2 x. ( D x. A ) )' % (f5, C10))],
             'eqtrd',
             '( %s x. ( %s x. ( D x. A ) ) ) = ( 2 x. ( D x. A ) )' % (f5, C10))
    w.qed([st([id4], 'eqcomd',
              '( 2 x. ( D x. A ) ) = ( %s x. ( %s x. ( D x. A ) ) )' % (f5, C10)), mul2],
          'eqbrtrd',
          '( %s -> ( 2 x. ( D x. A ) ) <_ ( %s x. ( ( D x. C ) / B ) ) )' % (EANT, f5))
    return w


GG = '( ( B / A ) x. ( %s x. C ) )' % K1
BANT = ('( ( A e. RR+ /\\ B e. RR+ ) /\\ ( C e. RR+ /\\ D e. RR+ ) /\\ '
        '( E e. RR+ /\\ %s <_ E ) )' % GG)
BGOAL = '( ( D / A ) / E ) <_ ( %s x. ( D / ( B x. C ) ) )' % K2


def btmain():
    w = W('btmain', 'The main term of the Brun-Titchmarsh assembly.')
    st = mkst(w, BANT)
    arp = st([], 'simp1l', 'A e. RR+')
    brp = st([], 'simp1r', 'B e. RR+')
    crp = st([], 'simp2l', 'C e. RR+')
    drp = st([], 'simp2r', 'D e. RR+')
    erp = st([], 'simp3l', 'E e. RR+')
    hyp = st([], 'simp3r', '%s <_ E' % GG)
    k1rp = st([num.rp(w, K1)], 'a1i', '%s e. RR+' % K1)
    k2rp = st([num.rp(w, K2)], 'a1i', '%s e. RR+' % K2)
    grp = st([st([brp, arp], 'rpdivcld', '( B / A ) e. RR+'),
              st([k1rp, crp], 'rpmulcld', '( %s x. C ) e. RR+' % K1)], 'rpmulcld',
             '%s e. RR+' % GG)
    darp = st([drp, arp], 'rpdivcld', '( D / A ) e. RR+')
    dare = st([darp], 'rpred', '( D / A ) e. RR')
    dage = st([darp, w.inst('rpge0')], 'syl', '0 <_ ( D / A )')
    divle = st([grp, erp, dare, dage, hyp], 'lediv2ad',
               '( ( D / A ) / E ) <_ ( ( D / A ) / %s )' % GG)
    qq = '( D / ( B x. C ) )'
    qrp = st([drp, st([brp, crp], 'rpmulcld', '( B x. C ) e. RR+')], 'rpdivcld',
             '%s e. RR+' % qq)
    k2q = st([k2rp, qrp], 'rpmulcld', '( %s x. %s ) e. RR+' % (K2, qq))
    mid = st([st([st([arp, brp], 'jca', '( A e. RR+ /\\ B e. RR+ )'),
                  st([crp, drp], 'jca', '( C e. RR+ /\\ D e. RR+ )')], 'jca', MANT),
              w.inst('mainid')], 'syl', '%s = ( D / A )' % MID)
    dmb = st([st([dare], 'recnd', '( D / A ) e. CC'),
              st([k2q], 'rpcnd', '( %s x. %s ) e. CC' % (K2, qq)),
              st([st([grp], 'rpcnd', '%s e. CC' % GG),
                  st([grp], 'rpne0d', '%s =/= 0' % GG)], 'jca',
                 '( %s e. CC /\\ %s =/= 0 )' % (GG, GG)), w.inst('divmul')], 'syl3anc',
             '( ( ( D / A ) / %s ) = ( %s x. %s ) <-> %s = ( D / A ) )' % (GG, K2, qq, MID))
    divval = st([dmb, mid], 'mpbird',
                '( ( D / A ) / %s ) = ( %s x. %s )' % (GG, K2, qq))
    w.qed([divle, divval], 'breqtrd', '( %s -> %s )' % (BANT, BGOAL))
    return w


def main(names=None):
    fns = {'mainid': mainid, 'errid': errid, 'btmain': btmain}
    ok = True
    for nm in (names or ['mainid', 'errid', 'btmain']):
        ok = fns[nm]().run() and ok
    return ok


if __name__ == '__main__':
    sys.exit(0 if main(sys.argv[1:] or None) else 1)
