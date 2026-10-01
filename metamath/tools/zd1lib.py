"""Sortie ZD1 helpers (Route Z: ZeroDensity.lean from the top).

STATEMENTS / HYPS are the frozen statements of ZD1-blueprint.md, one place,
so that the blueprint, the grammar check and the generators cannot drift apart.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from zbvlib import *
from lin import linarith, nlinarith, lineq
from zbv2lib import eqtr, le_lit2, bind, bind3
import num

# ---- the Detector parameters, written out (Detector.lean section 1)
C31 = '( ; 3 1 / ; 5 0 )'
C63 = '( ; 6 3 / ; ; 1 0 0 )'
Z1 = '( D ^c %s )' % C31                       # z1par D
Z2 = '( D ^c %s )' % C63                       # z2par D
XP = '( D ^c ( 6 / 5 ) )'                      # Xpar D
RP = '( D ^c ( 1 / ; ; 1 0 0 ) )'              # Rpar D
ELLD = '( ( 1 / ; ; 1 0 0 ) x. ( log ` D ) )'  # ellpar D
C5 = '; ; ; ; ; 5 0 0 0 0 0'
C12 = '; ; ; ; ; ; ; ; ; 1 0 0 0 0 0 0 0 0 0'   # C12 = 10 ^ 9
C12T = '( %s / 3 )' % C12
B1 = '( 1 - ( 2 x. T ) )'
B2 = '( 2 - ( 2 x. T ) )'
BA = lambda n: '( ( %s bvA %s ) ` %s )' % (Z1, Z2, n)          # bvA (z1par D) (z2par D) n
FN = lambda n: '( ( %s ^c %s ) x. ( %s ^ 2 ) )' % (n, B1, BA(n))  # f n of sigma_diag_le
EN = lambda n: '( exp ` ( -u %s / %s ) )' % (n, XP)             # e ^ ( - n / X )
HZD = '( D e. RR /\\ 1 < D /\\ ; ; 2 0 0 <_ ( log ` D ) )'
HT = '( T e. RR /\\ ( ( ; 9 9 / ; ; 1 0 0 ) <_ T /\\ T <_ 1 ) )'
H0 = '( %s /\\ %s )' % (HZD, HT)
PL = lambda x: 'if ( 1 <_ %s , ( log ` %s ) , 0 )' % (x, x)
BVL = lambda y: '( ( ( mmu ` %s ) x. ( %s - %s ) ) / ( log ` ( B / A ) ) )' % (y, PL('( B / %s )' % y), PL('( A / %s )' % y))
DV = lambda n: '{ x e. NN | x || %s }' % n
FL2 = lambda j: '( |_ ` ( ( 2 ^ %s ) x. %s ) )'                # not used directly
QRP = lambda N, R: 'prod_ p e. { q e. Prime | ( q || %s /\\ q <_ %s ) } ( 1 - ( 1 / p ) )' % (N, R)
XB = '( %s ^c %s )' % (XP, B2)                                   # X ^ ( 2 - 2 sigma )
EE = '( N x. ( T ^c C ) )'                                       # E = d t ^ c0

BLK_L = lambda J, X, A: 'sum_ n e. ( 1 ... ( |_ ` ( ( 2 ^ %s ) x. %s ) ) ) ( %s x. ( exp ` ( -u n / %s ) ) )' % (J, X, A, X)
BLK_R = lambda J, X, A: 'sum_ j e. ( 0 ... %s ) ( ( exp ` -u j ) x. sum_ n e. ( 1 ... ( |_ ` ( ( 2 ^ j ) x. %s ) ) ) %s )' % (J, X, A)

STATEMENTS = {
    # definitions' values
    'bvlamval': '( ( A e. V /\\ B e. W ) -> ( A bvLam B ) = ( z e. NN |-> %s ) )' % BVL('z'),
    'bvaval': '( ( ( A e. V /\\ B e. W ) /\\ N e. NN ) -> ( ( A bvA B ) ` N ) = sum_ d e. %s ( ( A bvLam B ) ` d ) )' % DV('N'),
    # I4* at the definition (the interface ZeroDensity.lean line 413 uses)
    'zdl2star': '( ( ( ( D e. RR /\\ 1 < D ) /\\ ( ; ; 1 0 0 <_ %s /\\ ( Y e. RR /\\ %s <_ Y ) ) ) /\\ ( T e. RR /\\ ( ( 1 / 2 ) <_ T /\\ T <_ 1 ) ) ) -> '
                'sum_ n e. ( 1 ... ( |_ ` Y ) ) ( ( n ^c %s ) x. ( %s ^ 2 ) ) <_ ( ( ( %s x. ( Y ^c %s ) ) x. ( log ` Y ) ) / %s ) )'
                % (Z1, Z1, B1, BA('n'), C5, B2, ELLD),
    # section 1 of ZeroDensity.lean
    'zdblocks': '( ( ph /\\ J e. NN0 ) -> %s <_ %s )' % (BLK_L('J', 'X', 'A'), BLK_R('J', 'X', 'A')),
    'zdje4': '( ( A e. RR /\\ 0 <_ A ) -> ( A x. ( exp ` ( -u A / 4 ) ) ) <_ 4 )',
    'zdblkw': '( ( ( X e. RR /\\ 1 <_ X ) /\\ ( B e. RR /\\ ( 0 <_ B /\\ B <_ ( 1 / ; 5 0 ) ) ) /\\ J e. NN0 ) -> '
              '( ( ( exp ` -u J ) x. ( ( ( 2 ^ J ) x. X ) ^c B ) ) x. ( log ` ( ( 2 ^ J ) x. X ) ) ) <_ '
              '( ( ( exp ` ( -u J / 4 ) ) x. ( X ^c B ) ) x. ( ( log ` X ) + 3 ) ) )',
    'zdgeo4': '( J e. NN0 -> sum_ j e. ( 0 ... J ) ( exp ` ( -u j / 4 ) ) <_ 5 )',
    'zdparams': '( %s -> ( ; ; 1 0 0 <_ %s /\\ %s <_ %s /\\ 1 <_ %s ) )' % (HZD, Z1, Z1, XP, XP),
    'zdhbound': '( ( %s /\\ J e. NN0 ) -> sum_ j e. ( 0 ... J ) ( ( exp ` -u j ) x. sum_ n e. ( 1 ... ( |_ ` ( ( 2 ^ j ) x. %s ) ) ) %s ) <_ ( %s x. %s ) )'
                % (H0, XP, FN('n'), C12T, XB),
    'zdsigfin': '( ( %s /\\ M e. NN ) -> sum_ n e. ( 1 ... M ) ( %s x. %s ) <_ ( %s x. %s ) )' % (H0, FN('n'), EN('n'), C12T, XB),
    'zdsigdiag': '( ph -> ( seq 1 ( + , F ) e. dom ~~> /\\ sum_ n e. NN ( F ` n ) <_ ( %s x. %s ) ) )' % (C12, XB),
    # sections 2-5: the real-variable content
    'zdprodtel': '( M e. NN -> prod_ n e. ( 2 ... M ) ( 1 - ( 1 / n ) ) = ( 1 / M ) )',
    'zdprodle': '( ph -> prod_ k e. B C <_ prod_ k e. A C )',
    'zdinvqr': '( ( N e. NN /\\ ( R e. RR /\\ 1 <_ R ) ) -> ( 1 / R ) <_ %s )' % QRP('N', 'R'),
    'zdqrsq': '( ( N e. NN /\\ ( D e. RR /\\ 1 < D ) ) -> ( D ^c ( ; 1 3 / ; ; 5 0 0 ) ) <_ ( ( %s ^ 2 ) x. ( D ^c ( ; 2 3 / ; ; 5 0 0 ) ) ) )' % QRP('N', RP),
    'zdxrpow': '( ( ( D e. RR /\\ 1 < D ) /\\ ( T e. RR /\\ ( ; 9 9 / ; ; 1 0 0 ) <_ T ) ) -> %s <_ ( D ^c ( ; 1 2 / ; ; 5 0 0 ) ) )' % XB,
    'zd10exp': '( ( A e. RR /\\ 0 <_ A ) -> ( 1 + A ) <_ ( ; 1 0 x. ( exp ` ( A / ; 1 0 ) ) ) )',
    'zdxexp': '( ( D e. RR+ /\\ T e. RR ) -> ( %s x. ( exp ` ( ( ( 1 - T ) x. ( log ` D ) ) / ; 1 0 ) ) ) = ( D ^c ( ( 5 / 2 ) x. ( 1 - T ) ) ) )' % XB,
    'zdgood': '( ( ( ( ( D e. RR /\\ 1 < D ) /\\ ( T e. RR /\\ T <_ 1 ) ) /\\ ( ( A e. RR /\\ 0 <_ A ) /\\ ( B e. RR /\\ 0 <_ B ) ) ) /\\ '
              '( ( ( J e. RR /\\ 0 <_ J ) /\\ J <_ ( B x. %s ) ) /\\ ( ( K e. RR /\\ 0 <_ K ) /\\ K <_ ( B x. %s ) ) ) ) -> '
              '( ( A x. ( 1 + ( ( 1 - T ) x. ( log ` D ) ) ) ) x. ( J + K ) ) <_ ( ( ; 2 0 x. ( A x. B ) ) x. ( D ^c ( ( 5 / 2 ) x. ( 1 - T ) ) ) ) )' % (XB, XB),
    'zdpar': '( ( ( ( ( J e. RR /\\ 0 <_ J ) /\\ ( V e. RR /\\ 0 < V ) ) /\\ ( ( A e. RR /\\ 0 <_ A ) /\\ B e. RR ) ) /\\ '
             '( ( ( J x. V ) ^ 2 ) <_ ( J x. ( A + ( J x. B ) ) ) /\\ B <_ ( ( V ^ 2 ) / 2 ) ) ) -> J <_ ( ( 2 x. A ) / ( V ^ 2 ) ) )',
    'zdlogev': '( ( ( A e. RR /\\ 0 <_ A ) /\\ ( B e. RR /\\ 0 < B ) ) -> E. u e. RR ( 1 <_ u /\\ A. v e. RR ( u <_ v -> ( A x. ( log ` v ) ) <_ ( v ^c B ) ) ) )',
    'zdthresh': '( ( ( A e. RR /\\ 0 <_ A ) /\\ ( B e. RR /\\ 0 <_ B ) ) -> E. u e. RR ( 1 <_ u /\\ A. v e. RR ( u <_ v -> '
                '( ; ; 2 0 0 <_ ( log ` v ) /\\ ( A x. ( log ` v ) ) <_ ( v ^c ( ; 7 9 / ; ; ; 4 0 0 0 ) ) /\\ ( B x. ( log ` v ) ) <_ ( v ^c ( ; 1 3 / ; ; 5 0 0 ) ) ) ) ) )',
    'zd2rpar': '( ( D e. RR+ /\\ ; ; 2 0 0 <_ ( log ` D ) ) -> 2 <_ %s )' % RP,
    'zdband': '( ( A e. RR+ /\\ B e. RR ) -> E. u e. RR ( ; ; 2 0 0 <_ u /\\ A. v e. RR ( u <_ v -> '
              '( ( log ` v ) <_ ( v / 4 ) /\\ ( ( log ` v ) ^ 2 ) <_ ( ( A ^ 2 ) x. v ) /\\ ( B + 3 ) <_ ( v / 2 ) ) ) ) )',
    'zdpow4': '( ( A e. RR /\\ 0 <_ A ) -> ( A ^ 4 ) <_ ( exp ` ( ( 5 / 2 ) x. A ) ) )',
    'zdscale': '( ( N e. NN /\\ ( T e. RR /\\ 2 <_ T ) /\\ ( C e. RR /\\ 1 <_ C ) ) -> ( N x. ( T + 2 ) ) <_ ( 2 x. %s ) )' % EE,
    'zdscale2': '( ( N e. NN /\\ ( T e. RR /\\ 2 <_ T ) /\\ ( C e. RR /\\ 1 <_ C ) ) -> 2 <_ %s )' % EE,
    'zdthmh': '( ( ( ( N e. NN /\\ ( T e. RR /\\ 2 <_ T ) /\\ ( C e. RR /\\ 1 <_ C ) ) /\\ ( ( P e. RR /\\ P <_ ( 7 / 2 ) ) /\\ '
              '( S e. RR /\\ ( ( 9 / ; 1 0 ) <_ S /\\ S <_ ( ; 9 9 / ; ; 1 0 0 ) ) ) ) ) /\\ ( ( K e. NN0 /\\ ( H e. RR /\\ 0 <_ H ) ) /\\ '
              '( Z e. RR /\\ Z <_ ( ( H x. ( %s ^c ( P x. ( 1 - S ) ) ) ) x. ( ( log ` ( N x. ( T + 2 ) ) ) ^ K ) ) ) ) ) -> '
              'Z <_ ( ( H x. ( ( ; ; 4 0 0 x. ( K + 1 ) ) ^ K ) ) x. ( %s ^c ( ( 9 / 2 ) x. ( 1 - S ) ) ) ) )' % (EE, EE),
}

SJ = lambda J: 'sum_ n e. ( 1 ... ( |_ ` ( ( 2 ^ %s ) x. %s ) ) ) %s' % (J, XP, FN('n'))
KK = '( ( %s x. ( %s x. ( ( log ` %s ) + 3 ) ) ) / %s )' % (C5, XB, XP, ELLD)
STATEMENTS['zdhterm'] = '( ( %s /\\ J e. NN0 ) -> ( ( exp ` -u J ) x. %s ) <_ ( %s x. ( exp ` ( -u J / 4 ) ) ) )' % (H0, SJ('J'), KK)
HABP = '( A e. RR+ /\\ B e. RR+ /\\ A < B )'
STATEMENTS['bvlamre'] = '( ( %s /\\ N e. NN ) -> ( ( A bvLam B ) ` N ) e. RR )' % HABP
STATEMENTS['bvare'] = '( ( %s /\\ N e. NN ) -> ( ( A bvA B ) ` N ) e. RR )' % HABP
STATEMENTS['zdz12'] = '( ( D e. RR /\\ 1 < D ) -> ( %s e. RR+ /\\ %s e. RR+ /\\ %s < %s ) )' % (Z1, Z2, Z1, Z2)
STATEMENTS['zdbvare'] = '( ( ( D e. RR /\\ 1 < D ) /\\ N e. NN ) -> %s e. RR )' % BA('N')
STATEMENTS['zdlogcxp'] = '( ( ( X e. RR /\\ 1 <_ X ) /\\ E e. RR+ ) -> ( log ` X ) <_ ( ( X ^c E ) / E ) )'
BAND3 = lambda v: '( ( log ` %s ) <_ ( %s / 4 ) /\\ ( ( log ` %s ) ^ 2 ) <_ ( ( A ^ 2 ) x. %s ) /\\ ( B + 3 ) <_ ( %s / 2 ) )' % (v, v, v, v, v)
STATEMENTS['zdbandpt'] = ('( ( ( A e. RR+ /\\ B e. RR ) /\\ ( V e. RR /\\ ( ; ; 2 0 0 <_ V /\\ ( ( ; 1 6 / ( A ^ 2 ) ) ^ 2 ) <_ V /\\ ( 2 x. ( B + 3 ) ) <_ V ) ) ) -> %s )'
                          % BAND3('V'))
STATEMENTS['zdcdet'] = ('( ( ( N e. NN /\\ T e. RR ) /\\ ( ( A e. RR /\\ ( P e. RR /\\ P =/= 0 ) ) /\\ ( E e. RR+ /\\ ( W e. RR+ /\\ E <_ ( 3 x. W ) ) ) ) ) -> '
                        '( ( ( ( ( A x. P ) x. E ) x. ( N ^c -u T ) ) ^ 2 ) / ( ( ( 1 / N ) x. ( P ^ 2 ) ) x. W ) ) <_ '
                        '( 3 x. ( ( ( N ^c ( 1 - ( 2 x. T ) ) ) x. ( A ^ 2 ) ) x. E ) ) )')
STATEMENTS['zdd2e'] = ('( ( ( D e. RR+ /\\ E e. RR ) /\\ ( ( 1 <_ E /\\ D <_ ( 2 x. E ) ) /\\ ( S e. RR /\\ ( ( ; 9 9 / ; ; 1 0 0 ) <_ S /\\ S <_ 1 ) ) ) ) -> '
                       '( D ^c ( ( 5 / 2 ) x. ( 1 - S ) ) ) <_ ( 2 x. ( E ^c ( ( 9 / 2 ) x. ( 1 - S ) ) ) ) )')
STATEMENTS['zdsqabs'] = ('( ( N e. NN /\\ ( T e. RR /\\ 1 <_ T ) ) -> ( ( ( ; ; ; 1 1 2 0 x. T ) x. N ) x. ( log ` ( N x. ( T + 2 ) ) ) ) <_ '
                         '( ; ; ; 1 1 2 0 x. ( ( N x. ( T + 2 ) ) ^ 2 ) ) )')
LAMZ = '( ( 1 - S ) x. L )'
LAM0 = '( ( ( log ` L ) + ( ( 6 / 5 ) x. %s ) ) + C )' % LAMZ
HLS = '( ( L e. RR /\\ ; ; 2 0 0 <_ L ) /\\ ( S e. RR /\\ ( ( ; 9 9 / ; ; 1 0 0 ) <_ S /\\ S <_ 1 ) ) )'
STATEMENTS['zdzc1'] = ('( ( %s /\\ ( ( A e. RR+ /\\ C e. RR ) /\\ ( ( ( log ` L ) <_ ( L / 4 ) /\\ ( ( log ` L ) ^ 2 ) <_ ( ( A ^ 2 ) x. L ) /\\ ( C + 3 ) <_ ( L / 2 ) ) '
                       '/\\ ( %s ^ 2 ) <_ L ) ) ) -> ( ( %s + 3 ) <_ L /\\ ( ( 1 - S ) x. ( log ` L ) ) <_ A ) )' % (HLS, LAMZ, LAM0))
STATEMENTS['zdzc2'] = ('( ( %s /\\ ( ( C e. RR /\\ 0 <_ C ) /\\ ( ( ( log ` L ) <_ ( L / 4 ) /\\ ( C + 3 ) <_ ( L / 2 ) ) /\\ ( 1 <_ ( log ` L ) /\\ L < ( %s ^ 2 ) ) ) ) ) -> '
                       '( 1 <_ %s /\\ ( ( ; ; ; 1 1 2 0 x. %s ) x. ( log ` ( %s + 2 ) ) ) <_ ( ; ; ; 1 1 2 0 x. ( exp ` ( ( 5 / 2 ) x. %s ) ) ) ) )' % (HLS, LAMZ, LAM0, LAM0, LAM0, LAMZ))
STATEMENTS['zdhnum'] = '( %s -> ( 5 x. %s ) <_ ( %s x. %s ) )' % (H0, KK, C12T, XB)

HYPS = {
    'zdblocks': [('1', '( ph -> X e. RR+ )'), ('2', '( ( ph /\\ n e. NN ) -> A e. RR )'), ('3', '( ( ph /\\ n e. NN ) -> 0 <_ A )')],
    'zdsigdiag': [('1', '( ph -> %s )' % HZD), ('2', '( ph -> %s )' % HT),
                  ('3', '( ( ph /\\ n e. NN ) -> ( F ` n ) e. RR )'), ('4', '( ( ph /\\ n e. NN ) -> 0 <_ ( F ` n ) )'),
                  ('5', '( ( ph /\\ n e. NN ) -> ( F ` n ) <_ ( 3 x. ( %s x. %s ) ) )' % (FN('n'), EN('n')))],
    'zdprodle': [('1', '( ph -> B e. Fin )'), ('2', '( ph -> A C_ B )'), ('3', '( ( ph /\\ k e. B ) -> C e. RR )'),
                 ('4', '( ( ph /\\ k e. B ) -> 0 <_ C )'), ('5', '( ( ph /\\ k e. B ) -> C <_ 1 )')],
}

ORDER = ['bvlamval', 'bvaval', 'bvlamre', 'bvare', 'zdz12', 'zdbvare', 'zdl2star', 'zdblocks', 'zdje4', 'zdblkw', 'zdgeo4', 'zdparams', 'zdhterm', 'zdhnum', 'zdhbound', 'zdsigfin', 'zdsigdiag',
         'zdprodtel', 'zdprodle', 'zdinvqr', 'zdqrsq', 'zdxrpow', 'zd10exp', 'zdxexp', 'zdgood', 'zdpar', 'zdlogcxp', 'zdlogev', 'zdthresh',
         'zd2rpar', 'zdbandpt', 'zdband', 'zdpow4', 'zdscale', 'zdscale2', 'zdthmh', 'zdcdet', 'zdd2e', 'zdsqabs', 'zdzc1', 'zdzc2']


def gramcheck(labels):
    """grammar-check frozen statements: a worksheet per label with the $e lines and a bare qed"""
    import mm as _MM, re as _re
    from c0lib import hyp
    out = {}
    for lab in labels:
        w = W('zd1g' + lab.replace('.', ''), 'grammar check of %s' % lab)
        for n, f in HYPS.get(lab, []):
            hyp(w, n, '%s.%s' % (lab, n), f)
        w.lines.append('qed:?:? |- %s' % STATEMENTS[lab])
        w.write()
        ok, text = _MM.run_mmj2(os.path.join(_MM.WSDIR, w.label + '.mmp'))
        bad = [l for l in text.split('\n') if _re.match(r'^E-', l) and 'incomplete' not in l.lower() and 'E-PA-0410' not in l]
        out[lab] = bad
        try:
            os.remove(os.path.join(_MM.WSDIR, w.label + '.mmp'))
        except OSError:
            pass
    return out


def hyps_of(w, lab):
    from c0lib import hyp
    return [hyp(w, n, '%s.%s' % (lab, n), f) for n, f in HYPS.get(lab, [])]


if __name__ == '__main__':
    r = gramcheck(sys.argv[1:] or ORDER)
    for k, v in r.items():
        print(('OK   ' if not v else 'FAIL ') + k)
        for l in v:
            print('   ', l[:300])


def a1c(w, ante, ref, f):
    """a closed fact lifted to ante"""
    return w.s([w.s([], ref, f)], 'a1i', '( %s -> %s )' % (ante, f))


def litr(w, ante, X):
    """( ante -> X e. RR ) for a literal"""
    return w.s([num.real(w, X)], 'a1i', '( %s -> %s e. RR )' % (ante, X))


def litle(w, ante, A, B, strict=False):
    return w.s([num.le_lit(w, A, B, strict=strict)], 'a1i', '( %s -> %s %s %s )' % (ante, A, '<' if strict else '<_', B))


def dfacts(w, ante, h):
    """from h: ( ante -> HZD ): D e. RR, 1 < D, 200 <_ log D, D e. RR+, log D e. RR, 0 < log D"""
    st = mkst(w, ante)
    dr = st([h], 'simp1d', 'D e. RR'); d1 = st([h], 'simp2d', '1 < D'); l200 = st([h], 'simp3d', '; ; 2 0 0 <_ ( log ` D )')
    drp = st([dr, linarith(w, ante, [d1], '0 < D', leaves={'D': dr})], 'elrpd', 'D e. RR+')
    lr = st([drp], 'relogcld', '( log ` D ) e. RR')
    return dict(dr=dr, d1=d1, l200=l200, drp=drp, lr=lr, dc=st([dr], 'recnd', 'D e. CC'), dne=st([drp], 'rpne0d', 'D =/= 0'))


def cxpD(w, ante, df, q):
    """( D ^c q ) = ( exp ` ( q x. ( log ` D ) ) ), and q e. RR, ( D ^c q ) e. RR+ for a literal q"""
    st = mkst(w, ante)
    qr = litr(w, ante, q)
    e = st([df['dc'], df['dne'], st([qr], 'recnd', '%s e. CC' % q)], 'cxpefd', '( D ^c %s ) = ( exp ` ( %s x. ( log ` D ) ) )' % (q, q))
    rp = st([df['drp'], qr], 'rpcxpcld', '( D ^c %s ) e. RR+' % q)
    return dict(eq=e, qr=qr, rp=rp, re=st([rp], 'rpred', '( D ^c %s ) e. RR' % q))


def h0facts(w, ante, h0):
    """from h0: ( ante -> H0 ): dfacts + T e. RR, 99/100 <_ T, T <_ 1, beta = ( 2 - ( 2 x. T ) ) e. RR, 0 <_ beta, beta <_ 1 / 50,
    1 / 2 <_ T, zdparams' three facts, XP e. RR+"""
    st = mkst(w, ante)
    hz = st([h0], 'simpld', HZD); ht = st([h0], 'simprd', HT)
    f = dfacts(w, ante, hz)
    tr = st([ht], 'simpld', 'T e. RR')
    t2 = st([ht], 'simprd', '( ( ; 9 9 / ; ; 1 0 0 ) <_ T /\\ T <_ 1 )')
    t99 = st([t2], 'simpld', '( ; 9 9 / ; ; 1 0 0 ) <_ T'); t1 = st([t2], 'simprd', 'T <_ 1')
    br = st([a1c(w, ante, '2re', '2 e. RR'), st([a1c(w, ante, '2re', '2 e. RR'), tr], 'remulcld', '( 2 x. T ) e. RR')], 'resubcld', '%s e. RR' % B2)
    b0 = linarith(w, ante, [t1], '0 <_ %s' % B2, leaves={'T': tr})
    b50 = linarith(w, ante, [t99], '%s <_ ( 1 / ; 5 0 )' % B2, leaves={'T': tr})
    th = linarith(w, ante, [t99], '( 1 / 2 ) <_ T', leaves={'T': tr})
    pr = st([hz, w.inst('zdparams')], 'syl', '( ; ; 1 0 0 <_ %s /\\ %s <_ %s /\\ 1 <_ %s )' % (Z1, Z1, XP, XP))
    z100 = st([pr], 'simp1d', '; ; 1 0 0 <_ %s' % Z1); zx = st([pr], 'simp2d', '%s <_ %s' % (Z1, XP)); x1 = st([pr], 'simp3d', '1 <_ %s' % XP)
    xp = cxpD(w, ante, f, '( 6 / 5 )')
    z = cxpD(w, ante, f, C31)
    f.update(dict(hz=hz, ht=ht, tr=tr, t99=t99, t1=t1, br=br, b0=b0, b50=b50, th=th, z100=z100, zx=zx, x1=x1, xprp=xp['rp'], xpr=xp['re'],
                  z1r=z['re'], z1rp=z['rp']))
    return f
