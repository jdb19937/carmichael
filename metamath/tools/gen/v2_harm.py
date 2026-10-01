"""Sortie v2: the harmonic-sum upper bound.

harmub  ( ( M e. NN /\\ D e. ( 1 ... M ) ) ->
            sum_ m e. ( 1 ... ( |_ ` ( M / D ) ) ) ( 1 / m ) <_ ( 1 + ( log ` M ) ) )
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from tm import W
from cl import Closure

MD = '( M / D )'
SUM = 'sum_ m e. ( 1 ... ( |_ ` %s ) ) ( 1 / m )' % MD
ANTE = '( M e. NN /\\ D e. ( 1 ... M ) )'


def harmub():
    w = W('harmub', 'The harmonic sum up to M / D is at most 1 + log M, for D in ( 1 ... M ).')
    A = ANTE
    def st(hyps, ref, f):
        return w.s(hyps, ref, '( %s -> %s )' % (A, f))
    m = st([], 'simpl', 'M e. NN')
    dfz = st([], 'simpr', 'D e. ( 1 ... M )')
    d = st([dfz, w.inst('elfznn')], 'syl', 'D e. NN')
    dle = st([dfz, w.inst('elfzle2')], 'syl', 'D <_ M')
    d1 = st([dfz, w.inst('elfzle1')], 'syl', '1 <_ D')
    mr = st([m], 'nnred', 'M e. RR')
    dr = st([d], 'nnred', 'D e. RR')
    drp = st([d], 'nnrpd', 'D e. RR+')
    mrp = st([m], 'nnrpd', 'M e. RR+')
    mdrp = st([mrp, drp], 'rpdivcld', '%s e. RR+' % MD)
    mdr = st([mdrp], 'rpred', '%s e. RR' % MD)
    ge1 = st([drp, mr, dle, w.inst('divge1')], 'syl3anc', '1 <_ %s' % MD)
    hb = st([mdr, ge1, w.inst('harmonicubnd')], 'syl2anc',
            '%s <_ ( ( log ` %s ) + 1 )' % (SUM, MD))
    lgd = st([mrp, drp, w.inst('relogdiv')], 'syl2anc',
             '( log ` %s ) = ( ( log ` M ) - ( log ` D ) )' % MD)
    lg0 = st([dr, d1, w.inst('logge0')], 'syl2anc', '0 <_ ( log ` D )')
    lgm = st([mrp], 'relogcld', '( log ` M ) e. RR')
    lgdc = st([drp], 'relogcld', '( log ` D ) e. RR')
    sub = st([lgm, lgdc, w.inst('subge02')], 'syl2anc',
             '( 0 <_ ( log ` D ) <-> ( ( log ` M ) - ( log ` D ) ) <_ ( log ` M ) )')
    s1 = st([sub, lg0], 'mpbid', '( ( log ` M ) - ( log ` D ) ) <_ ( log ` M )')
    s2 = st([lgd, s1], 'eqbrtrd', '( log ` %s ) <_ ( log ` M )' % MD)
    lgmd = st([mdrp], 'relogcld', '( log ` %s ) e. RR' % MD)
    one = w.s([], '1red', '( %s -> 1 e. RR )' % A)
    s3 = st([lgmd, lgm, one, s2], 'leadd1dd',
            '( ( log ` %s ) + 1 ) <_ ( ( log ` M ) + 1 )' % MD)
    c = Closure(w, A, {'M': ('NN', m), 'D': ('NN', d)})
    sre = c.mem(SUM, 'RR')
    reb = st([lgmd, one], 'readdcld', '( ( log ` %s ) + 1 ) e. RR' % MD)
    rec = st([lgm, one], 'readdcld', '( ( log ` M ) + 1 ) e. RR')
    s4 = st([sre, reb, rec, hb, s3], 'letrd', '%s <_ ( ( log ` M ) + 1 )' % SUM)
    lgmc = st([lgm], 'recnd', '( log ` M ) e. CC')
    onec = st([one], 'recnd', '1 e. CC')
    s5 = st([lgmc, onec], 'addcomd', '( ( log ` M ) + 1 ) = ( 1 + ( log ` M ) )')
    w.qed([s4, s5], 'breqtrd', '( %s -> %s <_ ( 1 + ( log ` M ) ) )' % (A, SUM))
    return w


if __name__ == '__main__':
    harmub().run()
