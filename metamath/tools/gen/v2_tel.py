"""Sortie v2: the telescoping sum  sum_ j e. ( 2 ... M ) ( 1 / ( j x. ( j - 1 ) ) ) <_ 1."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from tm import W

BODY = '( 1 / ( k - 1 ) )'
A = 'M e. NN'


def telsumlem():
    w = W('telsumlem', 'The telescoping identity for 1 / ( j - 1 ) - 1 / ( ( j + 1 ) - 1 ).')
    def st(hyps, ref, f, ante=A):
        return w.s(hyps, ref, '( %s -> %s )' % (ante, f))
    # the four substitution hypotheses of telfsum
    def subh(rhs, val):
        a = w.s([], 'oveq1', '( k = %s -> ( k - 1 ) = ( %s - 1 ) )' % (rhs, rhs))
        return w.s([a], 'oveq2d', '( k = %s -> ( 1 / ( k - 1 ) ) = ( 1 / ( %s - 1 ) ) )' % (rhs, rhs))
    h1 = subh('j', 'j')
    h2 = subh('( j + 1 )', '( j + 1 )')
    h3 = subh('2', '2')
    h4 = subh('( M + 1 )', '( M + 1 )')
    h5 = w.s([], 'nnz', '( M e. NN -> M e. ZZ )')
    # ( M + 1 ) e. ( ZZ>= ` 2 )
    z2 = w.s([], '2z', '2 e. ZZ')
    z2a = st([z2], 'a1i', '2 e. ZZ')
    m1z = st([h5, w.inst('peano2z')], 'syl', '( M + 1 ) e. ZZ')
    m1 = st([], 'nnge1', '1 <_ M')
    mr = st([], 'nnred', 'M e. RR')
    one = w.s([], '1red', '( %s -> 1 e. RR )' % A)
    add = st([one, mr, one, m1], 'leadd1dd', '( 1 + 1 ) <_ ( M + 1 )')
    e2 = w.s([], 'df-2', '2 = ( 1 + 1 )')
    e2a = st([e2], 'a1i', '2 = ( 1 + 1 )')
    le2 = st([e2a, add], 'eqbrtrd', '2 <_ ( M + 1 )')
    h6 = st([z2a, m1z, le2, w.inst('eluz2')], 'syl3anbrc', '( M + 1 ) e. ( ZZ>= ` 2 )')
    # ( ( M e. NN /\ k e. ( 2 ... ( M + 1 ) ) ) -> ( 1 / ( k - 1 ) ) e. CC )
    B = '( M e. NN /\\ k e. ( 2 ... ( M + 1 ) ) )'
    kfz = w.s([], 'simpr', '( %s -> k e. ( 2 ... ( M + 1 ) ) )' % B)
    kz = st([kfz, w.inst('elfzelz')], 'syl', 'k e. ZZ', B)
    kr = st([kz], 'zred', 'k e. RR', B)
    k2 = st([kfz, w.inst('elfzle1')], 'syl', '2 <_ k', B)
    oneb = w.s([], '1red', '( %s -> 1 e. RR )' % B)
    twob = w.s([], '2re', '2 e. RR')
    twoba = st([twob], 'a1i', '2 e. RR', B)
    k1r = st([kr, oneb], 'resubcld', '( k - 1 ) e. RR', B)
    # 0 < ( k - 1 ) from 2 <_ k
    zlt = w.s([], '0lt1', '0 < 1')
    zlta = st([zlt], 'a1i', '0 < 1', B)
    sub1 = st([twoba, kr, oneb, k2], 'lesub1dd', '( 2 - 1 ) <_ ( k - 1 )', B)
    e21 = w.s([], '2m1e1', '( 2 - 1 ) = 1')
    e21a = st([e21], 'a1i', '( 2 - 1 ) = 1', B)
    ge1 = st([e21a, sub1], 'eqbrtrrd', '1 <_ ( k - 1 )', B)
    pos = st([zlta, ge1], 'ltletrd', '0 < ( k - 1 )', B)
    ne0 = st([pos], 'gt0ne0d', '( k - 1 ) =/= 0', B)
    k1c = st([k1r], 'recnd', '( k - 1 ) e. CC', B)
    h7 = st([k1c, ne0], 'reccld', '( 1 / ( k - 1 ) ) e. CC', B)
    w.qed([h1, h2, h3, h4, h5, h6, h7], 'telfsum',
          '( %s -> sum_ j e. ( 2 ... M ) ( ( 1 / ( j - 1 ) ) - ( 1 / ( ( j + 1 ) - 1 ) ) ) '
          '= ( ( 1 / ( 2 - 1 ) ) - ( 1 / ( ( M + 1 ) - 1 ) ) ) )' % A)
    return w





def telsum():
    w = W('telsum', 'The telescoping bound: sum_ j e. ( 2 ... M ) 1 / ( j x. ( j - 1 ) ) is at most 1.')
    B = '( M e. NN /\\ j e. ( 2 ... M ) )'
    def stb(hyps, ref, f):
        return w.s(hyps, ref, '( %s -> %s )' % (B, f))
    jfz = w.s([], 'simpr', '( %s -> j e. ( 2 ... M ) )' % B)
    jz = stb([jfz, w.inst('elfzelz')], 'syl', 'j e. ZZ')
    j2a = stb([jfz, w.inst('elfzle1')], 'syl', '2 <_ j')
    jr0 = stb([jz], 'zred', 'j e. RR')
    z0lt2 = stb([w.s([], '2pos', '0 < 2')], 'a1i', '0 < 2')
    zre0 = w.s([], '0red', '( %s -> 0 e. RR )' % B)
    twor0 = stb([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR')
    j0 = stb([zre0, twor0, jr0, z0lt2, j2a], 'ltletrd', '0 < j')
    jnb = stb([w.s([], 'elnnz', '( j e. NN <-> ( j e. ZZ /\\ 0 < j ) )')], 'a1i',
              '( j e. NN <-> ( j e. ZZ /\\ 0 < j ) )')
    jn = stb([jnb, stb([jz, j0], 'jca', '( j e. ZZ /\\ 0 < j )')], 'mpbird', 'j e. NN')
    jr = stb([jn], 'nnred', 'j e. RR')
    jc = stb([jn], 'nncnd', 'j e. CC')
    jne = stb([jn], 'nnne0d', 'j =/= 0')
    j2 = stb([jfz, w.inst('elfzle1')], 'syl', '2 <_ j')
    one = w.s([], '1red', '( %s -> 1 e. RR )' % B)
    onec = stb([one], 'recnd', '1 e. CC')
    twor = twor0
    j1r = stb([jr, one], 'resubcld', '( j - 1 ) e. RR')
    sub1 = stb([twor, jr, one, j2], 'lesub1dd', '( 2 - 1 ) <_ ( j - 1 )')
    e21 = stb([w.s([], '2m1e1', '( 2 - 1 ) = 1')], 'a1i', '( 2 - 1 ) = 1')
    ge1 = stb([e21, sub1], 'eqbrtrrd', '1 <_ ( j - 1 )')
    pos = stb([stb([w.s([], '0lt1', '0 < 1')], 'a1i', '0 < 1'), ge1], 'ltletrd', '0 < ( j - 1 )')
    ne0 = stb([pos], 'gt0ne0d', '( j - 1 ) =/= 0')
    j1c = stb([j1r], 'recnd', '( j - 1 ) e. CC')
    # ( ( j + 1 ) - 1 ) = j
    pnc = stb([jc, onec, w.inst('pncan')], 'syl2anc', '( ( j + 1 ) - 1 ) = j')
    rw = stb([pnc], 'oveq2d', '( 1 / ( ( j + 1 ) - 1 ) ) = ( 1 / j )')
    lhs = stb([rw], 'oveq2d',
              '( ( 1 / ( j - 1 ) ) - ( 1 / ( ( j + 1 ) - 1 ) ) ) = ( ( 1 / ( j - 1 ) ) - ( 1 / j ) )')
    dsd = stb([onec, j1c, onec, jc, ne0, jne], 'divsubdivd',
              '( ( 1 / ( j - 1 ) ) - ( 1 / j ) ) = ( ( ( 1 x. j ) - ( 1 x. ( j - 1 ) ) ) / ( ( j - 1 ) x. j ) )')
    n1 = stb([jc], 'mullidd', '( 1 x. j ) = j')
    n2 = stb([j1c], 'mullidd', '( 1 x. ( j - 1 ) ) = ( j - 1 )')
    num = stb([n1, n2], 'oveq12d',
              '( ( 1 x. j ) - ( 1 x. ( j - 1 ) ) ) = ( j - ( j - 1 ) )')
    nc = stb([jc, onec, w.inst('nncan')], 'syl2anc', '( j - ( j - 1 ) ) = 1')
    num2 = stb([num, nc], 'eqtrd', '( ( 1 x. j ) - ( 1 x. ( j - 1 ) ) ) = 1')
    den = stb([j1c, jc], 'mulcomd', '( ( j - 1 ) x. j ) = ( j x. ( j - 1 ) )')
    fr = stb([num2, den], 'oveq12d',
             '( ( ( 1 x. j ) - ( 1 x. ( j - 1 ) ) ) / ( ( j - 1 ) x. j ) ) = ( 1 / ( j x. ( j - 1 ) ) )')
    term = stb([lhs, stb([dsd, fr], 'eqtrd',
               '( ( 1 / ( j - 1 ) ) - ( 1 / j ) ) = ( 1 / ( j x. ( j - 1 ) ) )')], 'eqtrd',
               '( ( 1 / ( j - 1 ) ) - ( 1 / ( ( j + 1 ) - 1 ) ) ) = ( 1 / ( j x. ( j - 1 ) ) )')
    # now under A = M e. NN
    def st(hyps, ref, f):
        return w.s(hyps, ref, '( %s -> %s )' % (A, f))
    seq = st([term], 'sumeq2dv',
             'sum_ j e. ( 2 ... M ) ( ( 1 / ( j - 1 ) ) - ( 1 / ( ( j + 1 ) - 1 ) ) ) '
             '= sum_ j e. ( 2 ... M ) ( 1 / ( j x. ( j - 1 ) ) )')
    lem = st([], 'telsumlem',
             'sum_ j e. ( 2 ... M ) ( ( 1 / ( j - 1 ) ) - ( 1 / ( ( j + 1 ) - 1 ) ) ) '
             '= ( ( 1 / ( 2 - 1 ) ) - ( 1 / ( ( M + 1 ) - 1 ) ) )')
    val = st([seq, lem], 'eqtr3d',
             'sum_ j e. ( 2 ... M ) ( 1 / ( j x. ( j - 1 ) ) ) = ( ( 1 / ( 2 - 1 ) ) - ( 1 / ( ( M + 1 ) - 1 ) ) )')
    mc = st([], 'nncnd', 'M e. CC')
    onea = w.s([], '1red', '( %s -> 1 e. RR )' % A)
    oneac = st([onea], 'recnd', '1 e. CC')
    pnc2 = st([mc, oneac, w.inst('pncan')], 'syl2anc', '( ( M + 1 ) - 1 ) = M')
    r2 = st([pnc2], 'oveq2d', '( 1 / ( ( M + 1 ) - 1 ) ) = ( 1 / M )')
    e21a = st([w.s([], '2m1e1', '( 2 - 1 ) = 1')], 'a1i', '( 2 - 1 ) = 1')
    r1a = st([e21a], 'oveq2d', '( 1 / ( 2 - 1 ) ) = ( 1 / 1 )')
    r1b = st([w.s([], '1div1e1', '( 1 / 1 ) = 1')], 'a1i', '( 1 / 1 ) = 1')
    r1 = st([r1a, r1b], 'eqtrd', '( 1 / ( 2 - 1 ) ) = 1')
    rhs = st([r1, r2], 'oveq12d',
             '( ( 1 / ( 2 - 1 ) ) - ( 1 / ( ( M + 1 ) - 1 ) ) ) = ( 1 - ( 1 / M ) )')
    val2 = st([val, rhs], 'eqtrd', 'sum_ j e. ( 2 ... M ) ( 1 / ( j x. ( j - 1 ) ) ) = ( 1 - ( 1 / M ) )')
    recre = st([], 'nnrecre', '( 1 / M ) e. RR')
    recge = st([], 'nnrecgt0', '0 < ( 1 / M )')
    recge0 = st([recge], 'ltled', '0 <_ ( 1 / M )')
    sg = st([onea, recre, w.inst('subge02')], 'syl2anc',
            '( 0 <_ ( 1 / M ) <-> ( 1 - ( 1 / M ) ) <_ 1 )')
    le = st([sg, recge0], 'mpbid', '( 1 - ( 1 / M ) ) <_ 1')
    w.qed([val2, le], 'eqbrtrd',
          '( %s -> sum_ j e. ( 2 ... M ) ( 1 / ( j x. ( j - 1 ) ) ) <_ 1 )' % A)
    return w


if __name__ == '__main__':
    import sys
    for f in sys.argv[1:] or ['telsumlem', 'telsum']:
        globals()[f]().run()
