"""T-MD: the budget arithmetic of the ` _le_B ` forms of TM/Canon.lean, at the N level
(bit lengths as NN0 class variables, alphabet-independent): ~ tmdquad (the quadratic
form of ~ tmbquad ), ~ tmdmulb (` mulC_le_B ` : ` ys.length * (4 xs.length + 6 ys.length
+ 14) + 4 xs.length + 7 ys.length + 9 <= B m ` for lengths at most ` m `), ~ tmddivb
(` canonDivBound_B ` , ` c = 14 ` , constant ` 37 ` ; ` divBound_B ` is its instance)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from tmdlib import *
from cl import Closure
from lin import linarith, nlinarith, lineq
import num

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL


def tmdquad():
    lab = 'tmdquad'
    ph = '( M e. NN0 /\\ C e. NN0 /\\ C <_ ; 6 4 )'
    w = W(lab, 'The quadratic budget ~ tmbquad with the square expanded: ` C ( M ^ 2 + 4 M + 4 ) <_ ( TMB ` M ) ` '
               'for ` C <_ 64 ` .  Lean: ` le_B_of_le_quad ` after ` nlinarith ` .')
    mn = w.s([], 'simp1', '( %s -> M e. NN0 )' % ph)
    tq = w.s([], 'tmbquad', '( %s -> ( C x. ( ( M + 2 ) ^ 2 ) ) <_ ( TMB ` M ) )' % ph)
    mc = w.s([mn], 'nn0cnd', '( %s -> M e. CC )' % ph)
    c2 = w.s([], '2cnd', '( %s -> 2 e. CC )' % ph)
    b2 = w.s([mc, c2, w.inst('binom2')], 'syl2anc', '( %s -> ( ( M + 2 ) ^ 2 ) = ( ( ( M ^ 2 ) + ( 2 x. ( M x. 2 ) ) ) + ( 2 ^ 2 ) ) )' % ph)
    sqv = w.s([mc], 'sqvald', '( %s -> ( M ^ 2 ) = ( M x. M ) )' % ph)
    s22 = w.s([], 'sq2', '( 2 ^ 2 ) = 4'); s22a = w.s([s22], 'a1i', '( %s -> ( 2 ^ 2 ) = 4 )' % ph)
    r, mid = w.rewrite('( ( ( M ^ 2 ) + ( 2 x. ( M x. 2 ) ) ) + ( 2 ^ 2 ) )', {'( M ^ 2 )': ('( M x. M )', sqv), '( 2 ^ 2 )': ('4', s22a)}, ph)
    assert mid == '( ( ( M x. M ) + ( 2 x. ( M x. 2 ) ) ) + 4 )', mid
    mr = w.s([mn], 'nn0red', '( %s -> M e. RR )' % ph)
    c = Closure(w, ph, {'M': mr})
    e = lineq(w, ph, mid, QUAD_M, closure=c)
    tot = w.s([w.s([b2, r], 'eqtrd', '( %s -> ( ( M + 2 ) ^ 2 ) = %s )' % (ph, mid)), e], 'eqtrd', '( %s -> ( ( M + 2 ) ^ 2 ) = %s )' % (ph, QUAD_M))
    o = w.s([tot], 'oveq2d', '( %s -> ( C x. ( ( M + 2 ) ^ 2 ) ) = ( C x. %s ) )' % (ph, QUAD_M))
    w.qed([o, tq], 'eqbrtrrd', ST_QUAD)
    return w.run()


def quadinst(w, ph, mn, Cl):
    """( ph -> ( Cl x. QUAD_M ) <_ ( TMB ` M ) ) for a literal Cl <_ 64, mn : ( ph -> M e. NN0 )"""
    cn = w.s([num.nn0(w, num.nat_value(Cl))], 'a1i', '( %s -> %s e. NN0 )' % (ph, Cl))
    le = w.s([num.le_lit(w, Cl, '; 6 4')], 'a1i', '( %s -> %s <_ ; 6 4 )' % (ph, Cl))
    return w.s([mn, cn, le, w.inst('tmdquad')], 'syl3anc', '( %s -> ( %s x. %s ) <_ ( TMB ` M ) )' % (ph, Cl, QUAD_M))


def tmbre(w, ph, mn):
    t = w.s([mn, w.inst('tmbcl')], 'syl', '( %s -> ( TMB ` M ) e. NN )' % ph)
    return w.s([t], 'nnred', '( %s -> ( TMB ` M ) e. RR )' % ph)


def tmdmulb():
    lab = 'tmdmulb'
    ph = '( ( A e. NN0 /\\ B e. NN0 /\\ M e. NN0 ) /\\ ( A <_ M /\\ B <_ M ) )'
    w = W(lab, 'The budget arithmetic of ` mulC_le_B ` (TM/Canon.lean) at the N level: the cost of '
               '` mulC ` on words of lengths ` A ` (multiplicand) and ` B ` (multiplier), both at most '
               '` M ` , is within ` ( TMB ` M ) ` (the ` mulC_runs ` bound ` B ( 4 A + 6 B + 14 ) + 4 A + '
               '7 B + 9 ` ; ~ tmdquad at ` 10 ` ).  T7 glues it to ~ tm2fml and ~ tm2fcan at the concrete '
               'alphabet with ~ encnatlenpow for the lengths.')
    l = w.s([], 'simpl', '( %s -> ( A e. NN0 /\\ B e. NN0 /\\ M e. NN0 ) )' % ph)
    an = w.s([l, w.inst('simp1')], 'syl', '( %s -> A e. NN0 )' % ph)
    bn = w.s([l, w.inst('simp2')], 'syl', '( %s -> B e. NN0 )' % ph)
    mn = w.s([l, w.inst('simp3')], 'syl', '( %s -> M e. NN0 )' % ph)
    ale = w.s([], 'simprl', '( %s -> A <_ M )' % ph)
    ble = w.s([], 'simprr', '( %s -> B <_ M )' % ph)
    ar, br, mr = [w.s([x], 'nn0red', '( %s -> %s e. RR )' % (ph, v)) for x, v in ((an, 'A'), (bn, 'B'), (mn, 'M'))]
    ag, bg, mg = [w.s([x], 'nn0ge0d', '( %s -> 0 <_ %s )' % (ph, v)) for x, v in ((an, 'A'), (bn, 'B'), (mn, 'M'))]
    tq = quadinst(w, ph, mn, '; 1 0')
    c = Closure(w, ph, {'A': ar, 'B': br, 'M': mr, '( TMB ` M )': tmbre(w, ph, mn)})
    nlinarith(w, ph, [ale, ble, ag, bg, mg, tq], '%s <_ ( TMB ` M )' % MULB_LHS, closure=c, name='qed')
    return w.run()


def tmddivb():
    lab = 'tmddivb'
    ph = '( ( A e. NN0 /\\ D e. NN0 /\\ M e. NN0 ) /\\ ( C e. NN0 /\\ C <_ ; 1 4 ) /\\ ( A <_ M /\\ D <_ M ) )'
    w = W(lab, 'The budget arithmetic of ` canonDivBound_B ` (TM/Canon.lean) at the N level: the cost '
               '` A ( 23 ( A + D ) + 60 ) + C ( A + D ) + 37 ` of the canonical division wrappers on words '
               'of lengths ` A ` (dividend) and ` D ` (divisor), both at most ` M ` , with ` C <_ 14 ` , is '
               'within ` ( TMB ` M ) ` (~ tmdquad at ` 46 ` ); ` divBound_B ` (` C <_ 9 ` , constant ` 28 `) '
               'is an instance.  T7 glues it to ~ tm2fdm , ~ tm2fdiv , ~ tm2fmod and ~ tm2fcan .')
    an = w.s([], 'simp11', '( %s -> A e. NN0 )' % ph)
    dn = w.s([], 'simp12', '( %s -> D e. NN0 )' % ph)
    mn = w.s([], 'simp13', '( %s -> M e. NN0 )' % ph)
    cn = w.s([], 'simp2l', '( %s -> C e. NN0 )' % ph)
    cle = w.s([], 'simp2r', '( %s -> C <_ ; 1 4 )' % ph)
    ale = w.s([], 'simp3l', '( %s -> A <_ M )' % ph)
    dle = w.s([], 'simp3r', '( %s -> D <_ M )' % ph)
    ar, dr, mr, cr = [w.s([x], 'nn0red', '( %s -> %s e. RR )' % (ph, v)) for x, v in ((an, 'A'), (dn, 'D'), (mn, 'M'), (cn, 'C'))]
    ag, dg, mg, cg = [w.s([x], 'nn0ge0d', '( %s -> 0 <_ %s )' % (ph, v)) for x, v in ((an, 'A'), (dn, 'D'), (mn, 'M'), (cn, 'C'))]
    tq = quadinst(w, ph, mn, '; 4 6')
    c = Closure(w, ph, {'A': ar, 'D': dr, 'M': mr, 'C': cr, '( TMB ` M )': tmbre(w, ph, mn)})
    nlinarith(w, ph, [ale, dle, cle, ag, dg, mg, cg, tq], '%s <_ ( TMB ` M )' % DIVB_LHS, closure=c, name='qed')
    return w.run()


if __name__ == '__main__':
    if want('tmdquad'): tmdquad()
    if want('tmdmulb'): tmdmulb()
    if want('tmddivb'): tmddivb()
