"""T7: the letters and the machine shape (blueprint D1, D3): a real number is
not a bit letter, the payload of a bit letter, DG = ( 0 ..^ 8 ), GK = Gamma',
and a lambda on TMSt typed into ( Y ^m S )."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t7lib import *

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

P11 = '<. 1P , 1P >.'


def e0r(w):
    """closed: <. 1P , 1P >. e. 0R"""
    c1 = w.s([], 'enrer', '~R Er ( P. X. P. )')
    c2 = w.s([], '1pr', '1P e. P.')
    c3 = w.s([c2, c2, w.inst('opelxpi')], 'mp2an', '%s e. ( P. X. P. )' % P11)
    c4 = w.s([c1, c3, w.inst('ecref')], 'mp2an', '%s e. [ %s ] ~R' % (P11, P11))
    c5 = w.s([], 'df-0r', '0R = [ %s ] ~R' % P11)
    return w.s([c4, c5], 'eleqtrri', '%s e. 0R' % P11)


def tmcnbit():
    lab = 'tmcnbit'
    ph = '( ( A e. RR /\\ B e. 2o ) /\\ A = <. C , B >. )'
    w = W(lab, 'A real number is not a pair whose second component is a bit: the second component of a real '
               'is ` 0R ` (~ df-r ), which is neither ` (/) ` nor ` 1o ` .  The alphabet ` Gamma\' ` mixes the '
               'numerals ` 0 2 3 4 ` with the bit letters ` <. 1 , b >. ` (~ df-gamma ); this is the only '
               'structural fact about set.mm\'s numbers the machine layer uses (blueprint D3).')
    a1 = w.s([], 'simpll', '( %s -> A e. RR )' % ph)
    a2 = w.s([], 'simplr', '( %s -> B e. 2o )' % ph)
    a3 = w.s([], 'simpr', '( %s -> A = <. C , B >. )' % ph)
    dfr = w.s([], 'df-r', 'RR = ( R. X. { 0R } )')
    a4 = w.s([a1, dfr], 'eleqtrdi', '( %s -> A e. ( R. X. { 0R } ) )' % ph)
    a5 = w.s([a3, a4], 'eqeltrrd', '( %s -> <. C , B >. e. ( R. X. { 0R } ) )' % ph)
    a6 = w.s([], 'opelxp', '( <. C , B >. e. ( R. X. { 0R } ) <-> ( C e. R. /\\ B e. { 0R } ) )')
    a7 = w.s([a5, a6], 'sylib', '( %s -> ( C e. R. /\\ B e. { 0R } ) )' % ph)
    a8 = w.s([a7], 'simprd', '( %s -> B e. { 0R } )' % ph)
    a9 = w.s([a8, w.inst('elsni')], 'syl', '( %s -> B = 0R )' % ph)
    a10 = w.s([a9, a2], 'eqeltrrd', '( %s -> 0R e. 2o )' % ph)
    a11 = w.s([a10, w.inst('bwel2o')], 'syl', '( %s -> ( 0R = (/) \\/ 0R = 1o ) )' % ph)
    e = e0r(w)
    # -. 0R = (/)
    b1 = w.s([], 'eleq2', '( 0R = (/) -> ( %s e. 0R <-> %s e. (/) ) )' % (P11, P11))
    b2 = w.s([e, b1], 'mpbii', '( 0R = (/) -> %s e. (/) )' % P11)
    b3 = w.s([], 'noel', '-. %s e. (/)' % P11)
    b4 = w.s([b3, b2], 'mto', '-. 0R = (/)')
    # -. 0R = 1o
    c1 = w.s([], 'eleq2', '( 0R = 1o -> ( %s e. 0R <-> %s e. 1o ) )' % (P11, P11))
    c2 = w.s([e, c1], 'mpbii', '( 0R = 1o -> %s e. 1o )' % P11)
    c3 = w.s([], 'df1o2', '1o = { (/) }')
    c4 = w.s([c2, c3], 'eleqtrdi', '( 0R = 1o -> %s e. { (/) } )' % P11)
    c5 = w.s([c4, w.inst('elsni')], 'syl', '( 0R = 1o -> %s = (/) )' % P11)
    c6 = w.s([], '1pr', '1P e. P.')
    c7 = w.s([c6], 'elexi', '1P e. _V')
    c8 = w.s([c7, c7], 'opnzi', '%s =/= (/)' % P11)
    dne = w.s([], 'df-ne', '( %s =/= (/) <-> -. %s = (/) )' % (P11, P11))
    c9 = w.s([c8, dne], 'mpbi', '-. %s = (/)' % P11)
    c10 = w.s([c9, c5], 'mto', '-. 0R = 1o')
    d1 = w.s([b4, c10], 'pm3.2i', '( -. 0R = (/) /\\ -. 0R = 1o )')
    d2 = w.s([], 'ioran', '( -. ( 0R = (/) \\/ 0R = 1o ) <-> ( -. 0R = (/) /\\ -. 0R = 1o ) )')
    d3 = w.s([d1, d2], 'mpbir', '-. ( 0R = (/) \\/ 0R = 1o )')
    d4 = w.s([d3, a11], 'mto', '-. %s' % ph)
    d5 = w.s([], 'imnan', '( ( ( A e. RR /\\ B e. 2o ) -> -. A = <. C , B >. ) <-> -. %s )' % ph)
    w.qed([d4, d5], 'mpbir', '( ( A e. RR /\\ B e. 2o ) -> -. A = <. C , B >. )')
    return w.run()


def tmcnbits():
    lab = 'tmcnbits'
    ph = 'A e. RR'
    w = W(lab, 'A real number is not a bit letter of ` Gamma\' ` (~ tmcnbit over the pairs of ` ( { 1 } X. 2o ) ` ): '
               'the terminator ` 4 ` and the marker ` 2 ` are distinguished from every bit by the handlers.')
    ph2 = '( A e. RR /\\ ( x e. { 1 } /\\ y e. 2o ) )'
    a1 = w.s([], 'simpl', '( %s -> A e. RR )' % ph2)
    a2 = w.s([], 'simprr', '( %s -> y e. 2o )' % ph2)
    a3 = w.s([a1, a2], 'jca', '( %s -> ( A e. RR /\\ y e. 2o ) )' % ph2)
    a4 = w.s([a3, w.inst('tmcnbit')], 'syl', '( %s -> -. A = <. x , y >. )' % ph2)
    a5 = w.s([a4], 'ralrimivva', '( %s -> A. x e. { 1 } A. y e. 2o -. A = <. x , y >. )' % ph)
    b1 = w.s([], 'ralnex', '( A. y e. 2o -. A = <. x , y >. <-> -. E. y e. 2o A = <. x , y >. )')
    b2 = w.s([b1], 'ralbii', '( A. x e. { 1 } A. y e. 2o -. A = <. x , y >. <-> A. x e. { 1 } -. E. y e. 2o A = <. x , y >. )')
    b3 = w.s([], 'ralnex', '( A. x e. { 1 } -. E. y e. 2o A = <. x , y >. <-> -. E. x e. { 1 } E. y e. 2o A = <. x , y >. )')
    b4 = w.s([b2, b3], 'bitri', '( A. x e. { 1 } A. y e. 2o -. A = <. x , y >. <-> -. E. x e. { 1 } E. y e. 2o A = <. x , y >. )')
    b5 = w.s([a5, b4], 'sylib', '( %s -> -. E. x e. { 1 } E. y e. 2o A = <. x , y >. )' % ph)
    b6 = w.s([], 'elxp2', '( A e. ( { 1 } X. 2o ) <-> E. x e. { 1 } E. y e. 2o A = <. x , y >. )')
    w.qed([b5, b6], 'sylnibr', '( %s -> -. A e. ( { 1 } X. 2o ) )' % ph)
    return w.run()


def tmcbit2():
    w = W('tmcbit2', 'The payload of a bit letter is a bit (Lean: ` Gamma\'.bit b ` with ` b : Bool ` ).')
    w.qed([], 'xp2nd', '( Z e. ( { 1 } X. 2o ) -> ( 2nd ` Z ) e. 2o )')
    return w.run()


def tmcbitop():
    lab = 'tmcbitop'
    ph = 'Z e. ( { 1 } X. 2o )'
    w = W(lab, 'A bit letter is the pair of ` 1 ` and its payload.')
    a1 = w.s([], '1st2nd2', '( %s -> Z = <. ( 1st ` Z ) , ( 2nd ` Z ) >. )' % ph)
    a2 = w.s([], 'xp1st', '( %s -> ( 1st ` Z ) e. { 1 } )' % ph)
    a3 = w.s([a2, w.inst('elsni')], 'syl', '( %s -> ( 1st ` Z ) = 1 )' % ph)
    a4 = w.s([a3], 'opeq1d', '( %s -> <. ( 1st ` Z ) , ( 2nd ` Z ) >. = <. 1 , ( 2nd ` Z ) >. )' % ph)
    w.qed([a1, a4], 'eqtrd', '( %s -> Z = <. 1 , ( 2nd ` Z ) >. )' % ph)
    return w.run()


def tmcdg():
    lab = 'tmcdg'
    ph = GEQ
    w = W(lab, 'The stack index set of the machine is ` ( 0 ..^ 8 ) ` (Lean: ` K := Fin 8 ` ).')
    fn = w.s([], 'tmgamfn', 'TMGam Fn ( 0 ..^ 8 )')
    dm = w.s([fn], 'fndmi', 'dom TMGam = ( 0 ..^ 8 )')
    dg = w.s([], 'dmeq', '( %s -> dom ( 1st ` ( 1st ` T ) ) = dom TMGam )' % ph)
    w.qed([dg, dm], 'eqtrdi', '( %s -> dom ( 1st ` ( 1st ` T ) ) = ( 0 ..^ 8 ) )' % ph)
    return w.run()


def tmcgk():
    lab = 'tmcgk'
    ph = '( %s /\\ K e. ( 0 ..^ 8 ) )' % GEQ
    w = W(lab, 'A stack index of the machine is an index of the type triple and its alphabet is ` Gamma\' ` .')
    geq = w.s([], 'simpl', '( %s -> %s )' % (ph, GEQ))
    kk = w.s([], 'simpr', '( %s -> K e. ( 0 ..^ 8 ) )' % ph)
    dg = w.s([geq, w.inst('tmcdg')], 'syl', '( %s -> dom ( 1st ` ( 1st ` T ) ) = ( 0 ..^ 8 ) )' % ph)
    kd = w.s([kk, dg], 'eleqtrrd', '( %s -> K e. dom ( 1st ` ( 1st ` T ) ) )' % ph)
    gv = w.s([geq], 'fveq1d', '( %s -> ( ( 1st ` ( 1st ` T ) ) ` K ) = ( TMGam ` K ) )' % ph)
    tg = w.s([kk, w.inst('tmgamfv')], 'syl', "( %s -> ( TMGam ` K ) = Gamma' )" % ph)
    ge = w.s([gv, tg], 'eqtrd', "( %s -> ( ( 1st ` ( 1st ` T ) ) ` K ) = Gamma' )" % ph)
    w.qed([kd, ge], 'jca', "( %s -> ( K e. dom ( 1st ` ( 1st ` T ) ) /\\ ( ( 1st ` ( 1st ` T ) ) ` K ) = Gamma' ) )" % ph)
    return w.run()


def tmcmapty():
    lab = 'tmcmapty'
    ph = '( %s /\\ Y e. V /\\ A. u e. TMSt X e. Y )' % SEQ
    F = '( u e. TMSt |-> X )'
    w = W(lab, 'A handler lambda ` fun v => X ` on the machine states, typed as a function into ` Y ` , is a '
               'member of ` ( Y ^m S ) ` : the form the statement constructors of ~ df-tm2stmt take '
               '(blueprint D2).')
    seq = w.s([], 'simp1', '( %s -> %s )' % (ph, SEQ))
    yv = w.s([], 'simp2', '( %s -> Y e. V )' % ph)
    al = w.s([], 'simp3', '( %s -> A. u e. TMSt X e. Y )' % ph)
    a1 = w.s([], 'fmpt', '( A. u e. TMSt X e. Y <-> %s : TMSt --> Y )' % F)
    a2 = w.s([al, a1], 'sylib', '( %s -> %s : TMSt --> Y )' % (ph, F))
    a3 = w.s([seq], 'feq2d', '( %s -> ( %s : ( 2nd ` T ) --> Y <-> %s : TMSt --> Y ) )' % (ph, F, F))
    a4 = w.s([a3, a2], 'mpbird', '( %s -> %s : ( 2nd ` T ) --> Y )' % (ph, F))
    tv = w.s([], 'fvexd', '( %s -> ( 2nd ` T ) e. _V )' % ph)
    a5 = w.s([yv, tv], 'elmapd', '( %s -> ( %s e. ( Y ^m ( 2nd ` T ) ) <-> %s : ( 2nd ` T ) --> Y ) )' % (ph, F, F))
    w.qed([a5, a4], 'mpbird', '( %s -> %s e. ( Y ^m ( 2nd ` T ) ) )' % (ph, F))
    return w.run()


if __name__ == '__main__':
    for l, f in [('tmcnbit', tmcnbit), ('tmcnbits', tmcnbits), ('tmcbit2', tmcbit2), ('tmcbitop', tmcbitop),
                 ('tmcdg', tmcdg), ('tmcgk', tmcgk), ('tmcmapty', tmcmapty)]:
        if want(l): f()
