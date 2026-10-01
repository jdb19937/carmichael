"""Sortie A4a, batch 5: divisorsOf (length, cost) and the modulus bridges."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from a4alib import *
import lin

only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

CSV = '( <" P "> ++ V )'
WN = '( Word NN0 X. NN0 )'
DV = '( 1st ` ( DivisorsOf ` V ) )'
MAV = '( 1st ` ( P MulAll %s ) )' % DV
CAT = '( %s ++ %s )' % (DV, MAV)

def s1ex(w, a, e):
    return w.s([w.s([w.s([], 's1cli', '<" %s "> e. Word _V' % e)], 'elexi', '<" %s "> e. _V' % e)], 'a1i',
               '( %s -> <" %s "> e. _V )' % (a, e)) if a else w.s([w.s([], 's1cli', '<" %s "> e. Word _V' % e)], 'elexi', '<" %s "> e. _V' % e)

def divctx(w, A):
    """context of a divisorsOf cons step"""
    vs = w.s([], 'simp1', '( %s -> V e. Word NN0 )' % A)
    pn = w.s([], 'simp2', '( %s -> P e. NN0 )' % A)
    cl = w.s([vs, w.inst('divisorsofcl')], 'syl', '( %s -> ( DivisorsOf ` V ) e. %s )' % (A, WN))
    d1, d2 = paircl(w, A, '( DivisorsOf ` V )', cl, 'Word NN0', 'NN0')
    mcl = w.s([pn, d1, w.inst('mulallcl')], 'syl2anc', '( %s -> ( P MulAll %s ) e. %s )' % (A, DV, WN))
    m1, m2 = paircl(w, A, '( P MulAll %s )' % DV, mcl, 'Word NN0', 'NN0')
    cs = w.s([pn, vs, w.inst('divisorsofcs')], 'syl2anc',
             '( %s -> ( DivisorsOf ` %s ) = <. %s , ( ( 2nd ` ( DivisorsOf ` V ) ) + ( 2nd ` ( P MulAll %s ) ) ) >. )' % (A, CSV, CAT, DV))
    xa = w.s([d1, m1, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word NN0 )' % (A, CAT))
    xb = w.s([d2, m2], 'nn0addcld', '( %s -> ( ( 2nd ` ( DivisorsOf ` V ) ) + ( 2nd ` ( P MulAll %s ) ) ) e. NN0 )' % (A, DV))
    lc = w.s([pn, vs, w.inst('alglencs')], 'syl2anc', '( %s -> ( # ` %s ) = ( ( # ` V ) + 1 ) )' % (A, CSV))
    lenn = w.s([vs, w.inst('lencl')], 'syl', '( %s -> ( # ` V ) e. NN0 )' % A)
    ml = w.s([pn, d1, w.inst('mulalllen')], 'syl2anc', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (A, MAV, DV))
    mc = w.s([pn, d1, w.inst('mulallcost')], 'syl2anc', '( %s -> ( 2nd ` ( P MulAll %s ) ) = ( # ` %s ) )' % (A, DV, DV))
    cat = w.s([d1, m1, w.inst('ccatlen')], 'syl2anc', '( %s -> ( # ` %s ) = ( ( # ` %s ) + ( # ` %s ) ) )' % (A, CAT, DV, MAV))
    ex = w.s([w.s([], '2cnd', '( %s -> 2 e. CC )' % A), lenn, w.inst('expp1')], 'syl2anc',
             '( %s -> ( 2 ^ ( ( # ` V ) + 1 ) ) = ( ( 2 ^ ( # ` V ) ) x. 2 ) )' % A)
    return vs, pn, d1, d2, m1, m2, cs, xa, xb, lc, lenn, ml, mc, cat, ex

# ======================================================================= divisorsOf length
PHI = '( # ` ( 1st ` ( DivisorsOf ` s ) ) ) = ( 2 ^ ( # ` s ) )'
def _b(w, goal):
    v = w.s([], 'divisorsof0', '( DivisorsOf ` (/) ) = <. <" 1 "> , 0 >.')
    e = w.s([v], 'fveq2i', '( 1st ` ( DivisorsOf ` (/) ) ) = ( 1st ` <. <" 1 "> , 0 >. )')
    o = w.s([s1ex(w, None, '1'), w.s([], 'c0ex', '0 e. _V')], 'op1st', '( 1st ` <. <" 1 "> , 0 >. ) = <" 1 ">')
    l = w.s([w.s([e, o], 'eqtri', '( 1st ` ( DivisorsOf ` (/) ) ) = <" 1 ">')], 'fveq2i',
            '( # ` ( 1st ` ( DivisorsOf ` (/) ) ) ) = ( # ` <" 1 "> )')
    l2 = w.s([l, w.s([], 's1len', '( # ` <" 1 "> ) = 1')], 'eqtri', '( # ` ( 1st ` ( DivisorsOf ` (/) ) ) ) = 1')
    r = w.s([w.s([w.s([], 'hash0', '( # ` (/) ) = 0')], 'oveq2i', '( 2 ^ ( # ` (/) ) ) = ( 2 ^ 0 )'),
             w.s([w.s([], '2cn', '2 e. CC'), w.inst('exp0')], 'ax-mp', '( 2 ^ 0 ) = 1')], 'eqtri', '( 2 ^ ( # ` (/) ) ) = 1')
    w.qed([l2, r], 'eqtr4i', goal)
def _s(w, A, ih, co):
    vs, pn, d1, d2, m1, m2, cs, xa, xb, lc, lenn, ml, mc, cat, ex = divctx(w, A)
    ihs = w.s([], 'simp3', '( %s -> %s )' % (A, ih))
    p1 = projeq(w, A, '( DivisorsOf ` %s )' % CSV, cs, CAT, '( ( 2nd ` ( DivisorsOf ` V ) ) + ( 2nd ` ( P MulAll %s ) ) )' % DV, xa, xb, 1)
    h1 = w.s([w.s([p1], 'fveq2d', '( %s -> ( # ` ( 1st ` ( DivisorsOf ` %s ) ) ) = ( # ` %s ) )' % (A, CSV, CAT)), cat], 'eqtrd',
             '( %s -> ( # ` ( 1st ` ( DivisorsOf ` %s ) ) ) = ( ( # ` %s ) + ( # ` %s ) ) )' % (A, CSV, DV, MAV))
    h2 = w.s([h1, w.s([ihs, w.s([ml, ihs], 'eqtrd', '( %s -> ( # ` %s ) = ( 2 ^ ( # ` V ) ) )' % (A, MAV))], 'oveq12d',
                  '( %s -> ( ( # ` %s ) + ( # ` %s ) ) = ( ( 2 ^ ( # ` V ) ) + ( 2 ^ ( # ` V ) ) ) )' % (A, DV, MAV))], 'eqtrd',
             '( %s -> ( # ` ( 1st ` ( DivisorsOf ` %s ) ) ) = ( ( 2 ^ ( # ` V ) ) + ( 2 ^ ( # ` V ) ) ) )' % (A, CSV))
    pw = w.s([w.s([], '2cnd', '( %s -> 2 e. CC )' % A), lenn], 'expcld', '( %s -> ( 2 ^ ( # ` V ) ) e. CC )' % A)
    dbl = w.s([pw], 'times2d', '( %s -> ( ( 2 ^ ( # ` V ) ) x. 2 ) = ( ( 2 ^ ( # ` V ) ) + ( 2 ^ ( # ` V ) ) ) )' % A)
    rr, _ = rweq(w, A, '( 2 ^ ( # ` %s ) )' % CSV, '( # ` %s )' % CSV, '( ( # ` V ) + 1 )', lc)
    w.qed([h2, w.s([w.s([rr, ex], 'eqtrd', '( %s -> ( 2 ^ ( # ` %s ) ) = ( ( 2 ^ ( # ` V ) ) x. 2 ) )' % (A, CSV)), dbl], 'eqtrd',
                   '( %s -> ( 2 ^ ( # ` %s ) ) = ( ( 2 ^ ( # ` V ) ) + ( 2 ^ ( # ` V ) ) ) )' % (A, CSV))], 'eqtr4d', '( %s -> %s )' % (A, co))
family(run, 'divisorsoflen', PHI, _b, _s, desc='The divisor enumeration has 2 ^ n entries (Lean: divisorsOf_length).', only=only)

# ======================================================================= divisorsOf cost
PHI = '( 2nd ` ( DivisorsOf ` s ) ) <_ ( 2 ^ ( # ` s ) )'
def _b(w, goal):
    v = w.s([], 'divisorsof0', '( DivisorsOf ` (/) ) = <. <" 1 "> , 0 >.')
    e = w.s([v], 'fveq2i', '( 2nd ` ( DivisorsOf ` (/) ) ) = ( 2nd ` <. <" 1 "> , 0 >. )')
    o = w.s([s1ex(w, None, '1'), w.s([], 'c0ex', '0 e. _V')], 'op2nd', '( 2nd ` <. <" 1 "> , 0 >. ) = 0')
    l = w.s([e, o], 'eqtri', '( 2nd ` ( DivisorsOf ` (/) ) ) = 0')
    r = w.s([w.s([w.s([], 'hash0', '( # ` (/) ) = 0')], 'oveq2i', '( 2 ^ ( # ` (/) ) ) = ( 2 ^ 0 )'),
             w.s([w.s([], '2cn', '2 e. CC'), w.inst('exp0')], 'ax-mp', '( 2 ^ 0 ) = 1')], 'eqtri', '( 2 ^ ( # ` (/) ) ) = 1')
    z1 = w.s([], '0le1', '0 <_ 1')
    w.qed([l, w.s([z1, r], 'breqtrri', '0 <_ ( 2 ^ ( # ` (/) ) )')], 'eqbrtri', goal)
def _s(w, A, ih, co):
    vs, pn, d1, d2, m1, m2, cs, xa, xb, lc, lenn, ml, mc, cat, ex = divctx(w, A)
    ihs = w.s([], 'simp3', '( %s -> %s )' % (A, ih))
    SUM = '( ( 2nd ` ( DivisorsOf ` V ) ) + ( 2nd ` ( P MulAll %s ) ) )' % DV
    p2 = projeq(w, A, '( DivisorsOf ` %s )' % CSV, cs, CAT, SUM, xa, xb, 2)
    dlv = w.s([vs, w.inst('divisorsoflen')], 'syl', '( %s -> ( # ` %s ) = ( 2 ^ ( # ` V ) ) )' % (A, DV))
    mc2 = w.s([mc, dlv], 'eqtrd', '( %s -> ( 2nd ` ( P MulAll %s ) ) = ( 2 ^ ( # ` V ) ) )' % (A, DV))
    p2b = w.s([p2, w.s([mc2], 'oveq2d', '( %s -> %s = ( ( 2nd ` ( DivisorsOf ` V ) ) + ( 2 ^ ( # ` V ) ) ) )' % (A, SUM))], 'eqtrd',
              '( %s -> ( 2nd ` ( DivisorsOf ` %s ) ) = ( ( 2nd ` ( DivisorsOf ` V ) ) + ( 2 ^ ( # ` V ) ) ) )' % (A, CSV))
    pwn = w.s([w.s([w.s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % A), lenn], 'nn0expcld', '( %s -> ( 2 ^ ( # ` V ) ) e. NN0 )' % A)
    pwr = w.s([pwn], 'nn0red', '( %s -> ( 2 ^ ( # ` V ) ) e. RR )' % A)
    d2r = w.s([d2], 'nn0red', '( %s -> ( 2nd ` ( DivisorsOf ` V ) ) e. RR )' % A)
    li = lin.linarith(w, A, [ihs], '( ( 2nd ` ( DivisorsOf ` V ) ) + ( 2 ^ ( # ` V ) ) ) <_ ( ( 2 ^ ( # ` V ) ) x. 2 )',
                      leaves={'( 2 ^ ( # ` V ) )': pwr, '( 2nd ` ( DivisorsOf ` V ) )': d2r})
    rr, _ = rweq(w, A, '( 2 ^ ( # ` %s ) )' % CSV, '( # ` %s )' % CSV, '( ( # ` V ) + 1 )', lc)
    rhs = w.s([rr, ex], 'eqtrd', '( %s -> ( 2 ^ ( # ` %s ) ) = ( ( 2 ^ ( # ` V ) ) x. 2 ) )' % (A, CSV))
    w.qed([w.s([p2b, li], 'eqbrtrd', '( %s -> ( 2nd ` ( DivisorsOf ` %s ) ) <_ ( ( 2 ^ ( # ` V ) ) x. 2 ) )' % (A, CSV)), rhs], 'breqtrrd',
          '( %s -> %s )' % (A, co))
family(run, 'divisorsofcost', PHI, _b, _s, desc='The cost of the divisor enumeration (Lean: divisorsOf_cost).', only=only)

# ======================================================================= lmodwrd, xceilwrd
if not only or 'lmodwrd' in only:
    w = W('lmodwrd', 'The modulus of the entries of a duplicate-free word is the product of the word (Lean: Lmod_toFinset).')
    T = "( W e. Word NN0 /\\ Fun `' W )"
    ws = w.s([], 'simpl', '( %s -> W e. Word NN0 )' % T)
    fu = w.s([], 'simpr', "( %s -> Fun `' W )" % T)
    fi = w.s([ws, w.inst('algwrdfi')], 'syl', '( %s -> ran W e. Fin )' % T)
    ffn = w.s([ws, w.inst('wrdf')], 'syl', '( %s -> W : ( 0 ..^ ( # ` W ) ) --> NN0 )' % T)
    ssn = w.s([ffn, w.inst('frn')], 'syl', '( %s -> ran W C_ NN0 )' % T)
    pw = w.s([w.s([], 'nn0ex', 'NN0 e. _V')], 'elpw2', '( ran W e. ~P NN0 <-> ran W C_ NN0 )')
    pw = w.s([pw], 'a1i', '( %s -> ( ran W e. ~P NN0 <-> ran W C_ NN0 ) )' % T)
    pwm = w.s([pw, ssn], 'mpbird', '( %s -> ran W e. ~P NN0 )' % T)
    fpw = w.s([pwm, fi], 'elind', '( %s -> ran W e. ( ~P NN0 i^i Fin ) )' % T)
    lv = w.s([fpw, w.inst('lmodqval')], 'syl', '( %s -> ( Lmod ` ran W ) = prod_ q e. ran W q )' % T)
    pr = w.s([ws, fu, w.inst('algprodrn')], 'syl2anc', '( %s -> %s = prod_ q e. ran W q )' % (T, PRD('W')))
    w.qed([lv, pr], 'eqtr4d', '( %s -> ( Lmod ` ran W ) = %s )' % (T, PRD('W')))
    run(w)

if not only or 'xceilwrd' in only:
    w = W('xceilwrd', 'The prime-search ceiling of the entries of a duplicate-free word (Lean: xceil_toFinset).')
    T = "( W e. Word NN0 /\\ Fun `' W )"
    ws = w.s([], 'simpl', '( %s -> W e. Word NN0 )' % T)
    ffn = w.s([ws, w.inst('wrdf')], 'syl', '( %s -> W : ( 0 ..^ ( # ` W ) ) --> NN0 )' % T)
    ssn = w.s([ffn, w.inst('frn')], 'syl', '( %s -> ran W C_ NN0 )' % T)
    pw = w.s([w.s([], 'nn0ex', 'NN0 e. _V')], 'elpw2', '( ran W e. ~P NN0 <-> ran W C_ NN0 )')
    pw = w.s([pw], 'a1i', '( %s -> ( ran W e. ~P NN0 <-> ran W C_ NN0 ) )' % T)
    pwm = w.s([pw, ssn], 'mpbird', '( %s -> ran W e. ~P NN0 )' % T)
    fi = w.s([ws, w.inst('algwrdfi')], 'syl', '( %s -> ran W e. Fin )' % T)
    fpw = w.s([pwm, fi], 'elind', '( %s -> ran W e. ( ~P NN0 i^i Fin ) )' % T)
    xv = w.s([fpw, w.inst('xceilval')], 'syl', '( %s -> ( xceil ` ran W ) = ( ( Lmod ` ran W ) ^ 5 ) )' % T)
    lm = w.s([], 'lmodwrd', '( %s -> ( Lmod ` ran W ) = %s )' % (T, PRD('W')))
    w.qed([xv, w.s([lm], 'oveq1d', '( %s -> ( ( Lmod ` ran W ) ^ 5 ) = ( %s ^ 5 ) )' % (T, PRD('W')))], 'eqtrd',
          '( %s -> ( xceil ` ran W ) = ( %s ^ 5 ) )' % (T, PRD('W')))
    run(w)
