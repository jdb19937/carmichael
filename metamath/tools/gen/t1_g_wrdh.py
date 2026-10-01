"""T1: the word lemmas the scan loops of the machine layer need."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t1lib import *

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

TL = lambda x: '( %s substr <. 1 , ( # ` %s ) >. )' % (x, x)


def ccatn0():
    lab = 'ccatn0'
    ph = '( U e. Word A /\\ U =/= (/) /\\ W e. Word A )'
    w = W(lab, 'A concatenation with a nonempty left factor is nonempty.')
    uw = w.s([], 'simp1', '( %s -> U e. Word A )' % ph)
    un = w.s([], 'simp2', '( %s -> U =/= (/) )' % ph)
    ww = w.s([], 'simp3', '( %s -> W e. Word A )' % ph)
    cc = w.s([uw, ww, w.inst('ccatcl')], 'syl2anc', '( %s -> ( U ++ W ) e. Word A )' % ph)
    ln = w.s([uw, ww, w.inst('ccatlen')], 'syl2anc', '( %s -> ( # ` ( U ++ W ) ) = ( ( # ` U ) + ( # ` W ) ) )' % ph)
    g1 = w.s([uw, w.inst('wrdlenge1n0')], 'syl', '( %s -> ( U =/= (/) <-> 1 <_ ( # ` U ) ) )' % ph)
    l1 = w.s([g1, un], 'mpbid', '( %s -> 1 <_ ( # ` U ) )' % ph)
    ur = w.s([uw, w.inst('lencl')], 'syl', '( %s -> ( # ` U ) e. NN0 )' % ph)
    wr = w.s([ww, w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % ph)
    urr = w.s([ur], 'nn0red', '( %s -> ( # ` U ) e. RR )' % ph)
    wrr = w.s([wr], 'nn0red', '( %s -> ( # ` W ) e. RR )' % ph)
    w0 = w.s([wr], 'nn0ge0d', '( %s -> 0 <_ ( # ` W ) )' % ph)
    from lin import linarith
    le = linarith(w, ph, [l1, w0], '1 <_ ( ( # ` U ) + ( # ` W ) )', leaves={'( # ` U )': urr, '( # ` W )': wrr})
    le2 = w.s([le, ln], 'breqtrrd', '( %s -> 1 <_ ( # ` ( U ++ W ) ) )' % ph)
    g2 = w.s([cc, w.inst('wrdlenge1n0')], 'syl', '( %s -> ( ( U ++ W ) =/= (/) <-> 1 <_ ( # ` ( U ++ W ) ) ) )' % ph)
    w.qed([g2, le2], 'mpbird', '( %s -> ( U ++ W ) =/= (/) )' % ph)
    return w.run()


def wrdtlcc():
    lab = 'wrdtlcc'
    ph = '( U e. Word A /\\ U =/= (/) /\\ W e. Word A )'
    w = W(lab, 'The tail of a concatenation with a nonempty left factor: the '
               'step every scan loop of the machine layer takes on its input '
               'stack.')
    uw = w.s([], 'simp1', '( %s -> U e. Word A )' % ph)
    un = w.s([], 'simp2', '( %s -> U =/= (/) )' % ph)
    ww = w.s([], 'simp3', '( %s -> W e. Word A )' % ph)
    cc = w.s([uw, ww, w.inst('ccatcl')], 'syl2anc', '( %s -> ( U ++ W ) e. Word A )' % ph)
    cn = w.s([uw, un, ww, w.inst('ccatn0')], 'syl3anc', '( %s -> ( U ++ W ) =/= (/) )' % ph)
    h1 = w.s([cc, cn, w.inst('wrdhdtl')], 'syl2anc',
             '( %s -> ( U ++ W ) = ( <" ( ( U ++ W ) ` 0 ) "> ++ %s ) )' % (ph, TL('( U ++ W )')))
    unn = w.s([uw, un, w.inst('lennncl')], 'syl2anc', '( %s -> ( # ` U ) e. NN )' % ph)
    upos = w.s([unn, w.inst('nngt0')], 'syl', '( %s -> 0 < ( # ` U ) )' % ph)
    fv = w.s([uw, ww, upos, w.inst('ccatfv0')], 'syl3anc', '( %s -> ( ( U ++ W ) ` 0 ) = ( U ` 0 ) )' % ph)
    s1e = w.s([fv], 's1eqd', '( %s -> <" ( ( U ++ W ) ` 0 ) "> = <" ( U ` 0 ) "> )' % ph)
    h2 = w.s([s1e], 'oveq1d', '( %s -> ( <" ( ( U ++ W ) ` 0 ) "> ++ %s ) = ( <" ( U ` 0 ) "> ++ %s ) )'
             % (ph, TL('( U ++ W )'), TL('( U ++ W )')))
    h3 = w.s([h1, h2], 'eqtrd', '( %s -> ( U ++ W ) = ( <" ( U ` 0 ) "> ++ %s ) )' % (ph, TL('( U ++ W )')))
    k1 = w.s([uw, un, w.inst('wrdhdtl')], 'syl2anc', '( %s -> U = ( <" ( U ` 0 ) "> ++ %s ) )' % (ph, TL('U')))
    k2 = w.s([k1], 'oveq1d', '( %s -> ( U ++ W ) = ( ( <" ( U ` 0 ) "> ++ %s ) ++ W ) )' % (ph, TL('U')))
    u0 = w.s([uw, un, w.inst('wrdfv0')], 'syl2anc', '( %s -> ( U ` 0 ) e. A )' % ph)
    s1c = w.s([u0], 's1cld', '( %s -> <" ( U ` 0 ) "> e. Word A )' % ph)
    tlc = w.s([uw, w.inst('swrdcl')], 'syl', '( %s -> %s e. Word A )' % (ph, TL('U')))
    k3 = w.s([s1c, tlc, ww, w.inst('ccatass')], 'syl3anc',
             '( %s -> ( ( <" ( U ` 0 ) "> ++ %s ) ++ W ) = ( <" ( U ` 0 ) "> ++ ( %s ++ W ) ) )' % (ph, TL('U'), TL('U')))
    k4 = w.s([k2, k3], 'eqtrd', '( %s -> ( U ++ W ) = ( <" ( U ` 0 ) "> ++ ( %s ++ W ) ) )' % (ph, TL('U')))
    eq = w.s([h3, k4], 'eqtr3d', '( %s -> ( <" ( U ` 0 ) "> ++ %s ) = ( <" ( U ` 0 ) "> ++ ( %s ++ W ) ) )'
             % (ph, TL('( U ++ W )'), TL('U')))
    tlcc = w.s([cc, w.inst('swrdcl')], 'syl', '( %s -> %s e. Word A )' % (ph, TL('( U ++ W )')))
    tlw = w.s([tlc, ww, w.inst('ccatcl')], 'syl2anc', '( %s -> ( %s ++ W ) e. Word A )' % (ph, TL('U')))
    can = w.s([tlcc, tlw, s1c, w.inst('ccatlcan')], 'syl3anc',
              '( %s -> ( ( <" ( U ` 0 ) "> ++ %s ) = ( <" ( U ` 0 ) "> ++ ( %s ++ W ) ) <-> %s = ( %s ++ W ) ) )'
              % (ph, TL('( U ++ W )'), TL('U'), TL('( U ++ W )'), TL('U')))
    w.qed([can, eq], 'mpbid', '( %s -> %s = ( %s ++ W ) )' % (ph, TL('( U ++ W )'), TL('U')))
    return w.run()


def s1tl():
    lab = 's1tl'
    w = W(lab, 'The tail of a one-letter word is empty.')
    ph = 'Y e. A'
    yy = w.s([], 'id', '( %s -> Y e. A )' % ph)
    sc = w.s([yy], 's1cld', '( %s -> <" Y "> e. Word A )' % ph)
    tlc = w.s([sc, w.inst('swrdcl')], 'syl', '( %s -> %s e. Word A )' % (ph, TL('<" Y ">')))
    nz = w.s([], 's1nz', '<" Y "> =/= (/)')
    nza = w.s([nz], 'a1i', '( %s -> <" Y "> =/= (/) )' % ph)
    ln = w.s([sc, nza, w.inst('wrdtllen')], 'syl2anc',
             '( %s -> ( # ` %s ) = ( ( # ` <" Y "> ) - 1 ) )' % (ph, TL('<" Y ">')))
    s1l = w.s([], 's1len', '( # ` <" Y "> ) = 1')
    s1la = w.s([s1l], 'a1i', '( %s -> ( # ` <" Y "> ) = 1 )' % ph)
    o1 = w.s([s1la], 'oveq1d', '( %s -> ( ( # ` <" Y "> ) - 1 ) = ( 1 - 1 ) )' % ph)
    m1 = w.s([], '1m1e0', '( 1 - 1 ) = 0')
    m1a = w.s([m1], 'a1i', '( %s -> ( 1 - 1 ) = 0 )' % ph)
    l0 = w.s([ln, w.s([o1, m1a], 'eqtrd', '( %s -> ( ( # ` <" Y "> ) - 1 ) = 0 )' % ph)], 'eqtrd',
             '( %s -> ( # ` %s ) = 0 )' % (ph, TL('<" Y ">')))
    tv = w.s([tlc], 'elexd', '( %s -> %s e. _V )' % (ph, TL('<" Y ">')))
    bi = w.s([tv, w.inst('hasheq0')], 'syl', '( %s -> ( ( # ` %s ) = 0 <-> %s = (/) ) )'
             % (ph, TL('<" Y ">'), TL('<" Y ">')))
    w.qed([bi, l0], 'mpbid', '( %s -> %s = (/) )' % (ph, TL('<" Y ">')))
    return w.run()


def wrdtls1():
    lab = 'wrdtls1'
    ph = '( Y e. A /\\ W e. Word A )'
    CY = '( <" Y "> ++ W )'
    w = W(lab, 'The tail of a word whose first letter is explicit.')
    yy = w.s([], 'simpl', '( %s -> Y e. A )' % ph)
    ww = w.s([], 'simpr', '( %s -> W e. Word A )' % ph)
    sc = w.s([yy], 's1cld', '( %s -> <" Y "> e. Word A )' % ph)
    nz = w.s([], 's1nz', '<" Y "> =/= (/)')
    nza = w.s([nz], 'a1i', '( %s -> <" Y "> =/= (/) )' % ph)
    tc = w.s([sc, nza, ww, w.inst('wrdtlcc')], 'syl3anc',
             '( %s -> %s = ( %s ++ W ) )' % (ph, TL(CY), TL('<" Y ">')))
    t0 = w.s([yy, w.inst('s1tl')], 'syl', '( %s -> %s = (/) )' % (ph, TL('<" Y ">')))
    o1 = w.s([t0], 'oveq1d', '( %s -> ( %s ++ W ) = ( (/) ++ W ) )' % (ph, TL('<" Y ">')))
    l0 = w.s([ww, w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ W ) = W )' % ph)
    w.qed([tc, w.s([o1, l0], 'eqtrd', '( %s -> ( %s ++ W ) = W )' % (ph, TL('<" Y ">')))], 'eqtrd',
          '( %s -> %s = W )' % (ph, TL(CY)))
    return w.run()


def ccats1fv0():
    lab = 'ccats1fv0'
    ph = '( Y e. A /\\ W e. Word A )'
    CY = '( <" Y "> ++ W )'
    w = W(lab, 'The first letter of a word whose first letter is explicit.')
    yy = w.s([], 'simpl', '( %s -> Y e. A )' % ph)
    ww = w.s([], 'simpr', '( %s -> W e. Word A )' % ph)
    sc = w.s([yy], 's1cld', '( %s -> <" Y "> e. Word A )' % ph)
    s1l = w.s([], 's1len', '( # ` <" Y "> ) = 1')
    s1la = w.s([s1l], 'a1i', '( %s -> ( # ` <" Y "> ) = 1 )' % ph)
    p1 = w.s([], '0lt1', '0 < 1')
    p1a = w.s([p1], 'a1i', '( %s -> 0 < 1 )' % ph)
    pos = w.s([p1a, s1la], 'breqtrrd', '( %s -> 0 < ( # ` <" Y "> ) )' % ph)
    fv = w.s([sc, ww, pos, w.inst('ccatfv0')], 'syl3anc', '( %s -> ( %s ` 0 ) = ( <" Y "> ` 0 ) )' % (ph, CY))
    s1f = w.s([yy, w.inst('s1fv')], 'syl', '( %s -> ( <" Y "> ` 0 ) = Y )' % ph)
    w.qed([fv, s1f], 'eqtrd', '( %s -> ( %s ` 0 ) = Y )' % (ph, CY))
    return w.run()


if __name__ == '__main__':
    if want('ccatn0'): ccatn0()
    if want('wrdtlcc'): wrdtlcc()

    if want('s1tl'): s1tl()
    if want('wrdtls1'): wrdtls1()
    if want('ccats1fv0'): ccats1fv0()
