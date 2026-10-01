"""Sortie v3: the 3 ^ omega divisor-sum bound, from V2's divmean.

sum3omle  ( ( P e. NN /\\ ( mmu ` P ) =/= 0 /\\ D e. NN ) ->
              sum_ d e. { x e. NN | ( x || P /\\ x <_ D ) } ( 3 ^ ( # ` { q e. Prime | q || d } ) )
                <_ ( D x. ( ( 1 + ( log ` D ) ) ^ 2 ) ) )
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm import W
from v3_lib import mkst
from cl import lift

A = '( P e. NN /\\ ( mmu ` P ) =/= 0 /\\ D e. NN )'
BSET = '{ x e. NN | ( x || P /\\ x <_ D ) }'
FZ = '( 1 ... D )'


def OMQ(v):
    return '( # ` { q e. Prime | q || %s } )' % v


def POW(v):
    return '( 3 ^ %s )' % OMQ(v)


def IFT(v):
    return 'if ( ( mmu ` %s ) =/= 0 , %s , 0 )' % (v, POW(v))


SUMB = 'sum_ d e. %s %s' % (BSET, POW('d'))
SUMBI = 'sum_ d e. %s %s' % (BSET, IFT('d'))
SUMF = 'sum_ d e. %s %s' % (FZ, IFT('d'))
RHS = '( D x. ( ( 1 + ( log ` D ) ) ^ 2 ) )'


def omfacts(w, ante, v, vnn):
    """( ante -> OMQ( v ) e. NN0 ) from ( ante -> v e. NN )"""
    f = mkst(w, ante)
    sbq = w.s([], 'breq1', '( p = q -> ( p || %s <-> q || %s ) )' % (v, v))
    cb = w.s([sbq], 'cbvrabv', '{ p e. Prime | p || %s } = { q e. Prime | q || %s }' % (v, v))
    cbd = f([cb], 'a1i', '{ p e. Prime | p || %s } = { q e. Prime | q || %s }' % (v, v))
    fin0 = f([vnn, w.inst('prmdvdsfi')], 'syl', '{ p e. Prime | p || %s } e. Fin' % v)
    fin = f([cbd, fin0], 'eqeltrrd', '{ q e. Prime | q || %s } e. Fin' % v)
    return f([fin, w.inst('hashcl')], 'syl', '%s e. NN0' % OMQ(v))


def sum3omle():
    w = W('sum3omle', 'The 3 ^ omega sum over the divisors of a squarefree P that are at '
                      'most D is at most D times ( 1 + log D ) squared.')
    st = mkst(w, A)
    pnn = st([], 'simp1', 'P e. NN')
    psqf = st([], 'simp2', '( mmu ` P ) =/= 0')
    dnn = st([], 'simp3', 'D e. NN')
    # membership in BSET
    sb1 = w.s([], 'breq1', '( x = d -> ( x || P <-> d || P ) )')
    sb2 = w.s([], 'breq1', '( x = d -> ( x <_ D <-> d <_ D ) )')
    sb = w.s([sb1, sb2], 'anbi12d',
             '( x = d -> ( ( x || P /\\ x <_ D ) <-> ( d || P /\\ d <_ D ) ) )')
    elb = w.s([sb], 'elrab',
              '( d e. %s <-> ( d e. NN /\\ ( d || P /\\ d <_ D ) ) )' % BSET)
    AB = '( %s /\\ d e. %s )' % (A, BSET)
    sbx = mkst(w, AB)
    memb = sbx([sbx([elb], 'a1i', '( d e. %s <-> ( d e. NN /\\ ( d || P /\\ d <_ D ) ) )' % BSET),
                sbx([], 'simpr', 'd e. %s' % BSET)], 'mpbid',
               '( d e. NN /\\ ( d || P /\\ d <_ D ) )')
    bdnn = sbx([memb], 'simpld', 'd e. NN')
    brest = sbx([memb], 'simprd', '( d || P /\\ d <_ D )')
    bdvd = sbx([brest], 'simpld', 'd || P')
    # squarefreeness of d
    dsqf = sbx([sbx([lift(w, pnn, AB), bdnn, bdvd, w.inst('dvdssqf')], 'syl3anc',
                    '( ( mmu ` P ) =/= 0 -> ( mmu ` d ) =/= 0 )'),
                lift(w, psqf, AB)], 'mpd', '( mmu ` d ) =/= 0')
    ift = sbx([dsqf], 'iftrued', '%s = %s' % (IFT('d'), POW('d')))
    iftr = sbx([ift], 'eqcomd', '%s = %s' % (POW('d'), IFT('d')))
    seq = st([iftr], 'sumeq2dv', '%s = %s' % (SUMB, SUMBI))
    # BSET C_ ( 1 ... D )
    sb1x = w.s([], 'breq1', '( x = e -> ( x || P <-> e || P ) )')
    sb2x = w.s([], 'breq1', '( x = e -> ( x <_ D <-> e <_ D ) )')
    sbxx = w.s([sb1x, sb2x], 'anbi12d',
               '( x = e -> ( ( x || P /\\ x <_ D ) <-> ( e || P /\\ e <_ D ) ) )')
    elbx = w.s([sbxx], 'elrab',
               '( e e. %s <-> ( e e. NN /\\ ( e || P /\\ e <_ D ) ) )' % BSET)
    AE = '( %s /\\ e e. %s )' % (A, BSET)
    se = mkst(w, AE)
    meme = se([se([elbx], 'a1i', '( e e. %s <-> ( e e. NN /\\ ( e || P /\\ e <_ D ) ) )' % BSET),
               se([], 'simpr', 'e e. %s' % BSET)], 'mpbid',
              '( e e. NN /\\ ( e || P /\\ e <_ D ) )')
    ednn = se([meme], 'simpld', 'e e. NN')
    erest = se([meme], 'simprd', '( e || P /\\ e <_ D )')
    eled = se([erest], 'simprd', 'e <_ D')
    efz0 = se([ednn, lift(w, dnn, AE), eled], '3jca', '( e e. NN /\\ D e. NN /\\ e <_ D )')
    efz = se([efz0,
              se([w.s([], 'elfz1b', '( e e. %s <-> ( e e. NN /\\ D e. NN /\\ e <_ D ) )' % FZ)],
                 'a1i', '( e e. %s <-> ( e e. NN /\\ D e. NN /\\ e <_ D ) )' % FZ)],
             'mpbird', 'e e. %s' % FZ)
    impl = st([efz], 'ex', '( e e. %s -> e e. %s )' % (BSET, FZ))
    sub = st([impl], 'ssrdv', '%s C_ %s' % (BSET, FZ))
    # closures on ( 1 ... D )
    AD = '( %s /\\ d e. %s )' % (A, FZ)
    sd = mkst(w, AD)
    dnn2 = sd([sd([], 'simpr', 'd e. %s' % FZ), w.inst('elfznn')], 'syl', 'd e. NN')
    om0 = omfacts(w, AD, 'd', dnn2)
    three = sd([w.s([], '3re', '3 e. RR')], 'a1i', '3 e. RR')
    powre = sd([three, om0], 'reexpcld', '%s e. RR' % POW('d'))
    zre = sd([], '0red', '0 e. RR')
    iftre = sd([powre, zre], 'ifcld', '%s e. RR' % IFT('d'))
    thge0 = sd([sd([], '0red', '0 e. RR'), three,
                sd([w.s([], '3pos', '0 < 3')], 'a1i', '0 < 3')], 'ltled', '0 <_ 3')
    pow0 = sd([three, thge0, om0, w.inst('expge0')], 'syl3anc', '0 <_ %s' % POW('d'))
    b1 = w.s([], 'breq2', '( %s = %s -> ( 0 <_ %s <-> 0 <_ %s ) )' % (POW('d'), IFT('d'), POW('d'), IFT('d')))
    b2 = w.s([], 'breq2', '( 0 = %s -> ( 0 <_ 0 <-> 0 <_ %s ) )' % (IFT('d'), IFT('d')))
    h3 = w.s([pow0], 'adantr', '( ( %s /\\ ( mmu ` d ) =/= 0 ) -> 0 <_ %s )' % (AD, POW('d')))
    zle = w.s([], '0le0', '0 <_ 0')
    h4 = w.s([zle], 'a1i', '( ( %s /\\ -. ( mmu ` d ) =/= 0 ) -> 0 <_ 0 )' % AD)
    ift0 = w.s([b1, b2, h3, h4], 'ifbothda', '( %s -> 0 <_ %s )' % (AD, IFT('d')))
    fin = st([], 'fzfid', '%s e. Fin' % FZ)
    less = st([fin, iftre, ift0, sub], 'fsumless', '%s <_ %s' % (SUMBI, SUMF))
    # divmean at K = 3
    thnn = st([w.s([], '3nn', '3 e. NN')], 'a1i', '3 e. NN')
    dm = st([thnn, dnn, w.inst('divmean')], 'syl2anc',
            '%s <_ ( D x. ( ( 1 + ( log ` D ) ) ^ ( 3 - 1 ) ) )' % SUMF)
    e32 = st([w.s([], '3m1e2', '( 3 - 1 ) = 2')], 'a1i', '( 3 - 1 ) = 2')
    e1 = st([e32], 'oveq2d', '( ( 1 + ( log ` D ) ) ^ ( 3 - 1 ) ) = ( ( 1 + ( log ` D ) ) ^ 2 )')
    e2 = st([e1], 'oveq2d', '( D x. ( ( 1 + ( log ` D ) ) ^ ( 3 - 1 ) ) ) = %s' % RHS)
    dm2 = st([dm, e2], 'breqtrd', '%s <_ %s' % (SUMF, RHS))
    # assemble
    finb = st([fin, sub], 'ssfid', '%s e. Fin' % BSET)
    ABnn = omfacts(w, AB, 'd', bdnn)
    threeb = sbx([w.s([], '3re', '3 e. RR')], 'a1i', '3 e. RR')
    powreb = sbx([threeb, ABnn], 'reexpcld', '%s e. RR' % POW('d'))
    zreb = sbx([], '0red', '0 e. RR')
    iftreb = sbx([powreb, zreb], 'ifcld', '%s e. RR' % IFT('d'))
    sbre = st([finb, iftreb], 'fsumrecl', '%s e. RR' % SUMBI)
    sfre = st([fin, iftre], 'fsumrecl', '%s e. RR' % SUMF)
    drp = st([dnn], 'nnrpd', 'D e. RR+')
    dr = st([drp], 'rpred', 'D e. RR')
    lg = st([drp], 'relogcld', '( log ` D ) e. RR')
    one = st([], '1red', '1 e. RR')
    base = st([one, lg], 'readdcld', '( 1 + ( log ` D ) ) e. RR')
    sq = st([base], 'resqcld', '( ( 1 + ( log ` D ) ) ^ 2 ) e. RR')
    rhsre = st([dr, sq], 'remulcld', '%s e. RR' % RHS)
    tr = st([sbre, sfre, rhsre, less, dm2], 'letrd', '%s <_ %s' % (SUMBI, RHS))
    w.qed([seq, tr], 'eqbrtrd', '( %s -> %s <_ %s )' % (A, SUMB, RHS))
    return w


if __name__ == '__main__':
    sum3omle().run()
