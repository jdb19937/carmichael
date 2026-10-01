"""T13: the units from their definitions (Lean Step5 1975-2050, "the units" and "the unit bounds of the pieces").

  t13srcu0   from ` b1 = 5 ( T bs + 1 ) + bs + bn + 1 ` , ` U = B X0 ` with ` X0 = ( 111 ( T + 1 ) + 13 ( 2 ^ T + 2 ) ) b1 + 4 T + 200 ` ,
             ` V = E0 U ` with ` E0 = ( 2 ^ ( T bs + 1 ) ) ^ 2 ( 2 ^ T + 2 ) ` : every unit fact the assembly needs
             (~ tmblin , ~ tmbmono , ~ lemulge12 )

    MM_DB=sorties/t13.mm python3 tools/gen/t13_c_u0.py t13srcu0
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t13lib import *
from t13_b_help import pow2le, pow2lt, p2leaf, tmbleaf, tmbmono, lemul1a, SB5, UB1, E0_, WEQ
from t10_n_rgf import tmbn
from lin import linarith, lineq
from cl import Closure

SEL = sys.argv[1:]
P2U, EXXU, NPU, VXU, UP2, UN1, UN2S = P.P2U, P.EXXU, P.NPU, P.VXU, P.UP2, P.UN1, P.UN2S
SB1 = SB1_('U', 'B', 'H')
X0 = SX_('U', P2U, "B'")
BEQ = "B' = %s" % SB1
UEQ = "U' = ( TMB ` %s )" % X0
HB3U = "( TMB ` ( ( ( ( ; 4 8 x. ( U + 1 ) ) x. ( B' + B' ) ) + ( 4 x. U ) ) + ; ; 1 0 2 ) ) <_ U'"
CSC_ = '( TMB ` ( ( 3 x. ( B + H ) ) + 8 ) )'
CST_ = '( TMB ` ( ( ( ; 1 5 x. ( U + 1 ) ) x. B ) + ; 4 6 ) )'
T_U0 = ((('U e. NN0', 'B e. NN0', 'H e. NN0'), '2 <_ B'), (BEQ, UEQ, WEQ))
G3 = (("B' e. NN0", "%s <_ B'" % SB5), ("( ( 2 x. H ) + 4 ) <_ U'", "%s <_ U'" % CSC_, "%s <_ U'" % CST_))
G4 = ("( ( %s + 2 ) x. U' ) <_ W'" % P2U, "( TMB ` %s ) <_ U'" % EXXU)
G6 = (HB3U, "( B + 2 ) <_ U'", "( H + 2 ) <_ U'")
C_U0 = ((UN1, UN2S), (G3, G4), (UP2, G6))
add13('t13srcu0', T_U0, cj(C_U0))


def t13srcu0():
    lab = 't13srcu0'
    ph = cj(T_U0)
    w = W(lab, 'The units of Lean\'s ` searchF_le_B ` from their definitions (Step5 1975-2050): with ` b1 = 5 ( T bs + 1 ) + '
               'bs + bn + 1 ` , ` U = B X0 ` , ` X0 = ( 111 ( T + 1 ) + 13 ( 2 ^ T + 2 ) ) b1 + 4 T + 200 ` and ` V = E0 U ` , '
               'every bit bound of the pieces is at most ` U ` (~ tmbmono against ` X0 ` , ~ tmblin ), ` U <_ V ` , ` 8 <_ U ` .')
    s = w.s
    c = Ctx(w, ph, T_U0)
    un, bn, hn, b2, beq, ueq, weq = c['U e. NN0'], c['B e. NN0'], c['H e. NN0'], c['2 <_ B'], c[BEQ], c[UEQ], c[WEQ]
    cl = Closure(w, ph, {'U': ('NN0', un), 'B': ('NN0', bn), 'H': ('NN0', hn)})
    p2leaf(w, ph, cl, 'U')
    b1n = s([beq, cl.mem(SB1, 'NN0')], 'eqeltrd', "( %s -> B' e. NN0 )" % ph)
    cl.leaf("B'", 'NN0', b1n)
    x0n = cl.mem(X0, 'NN0')
    tmbleaf(w, ph, cl, X0)
    upn = s([ueq, cl.mem('( TMB ` %s )' % X0, 'NN0')], 'eqeltrd', "( %s -> U' e. NN0 )" % ph)
    cl.leaf("U'", 'NN0', upn)
    p2leaf(w, ph, cl, UB1)
    P2 = '( 2 ^ %s )' % UB1
    SQ = '( %s ^ 2 )' % P2
    sqn = s([s([closed(w, ph, '2nn', '2 e. NN'), cl.mem(UB1, 'NN0'), w.inst('nnexpcl')], 'syl2anc', '( %s -> %s e. NN )' % (ph, P2)), closed(w, ph, '2nn0', '2 e. NN0'), w.inst('nnexpcl')],
            'syl2anc', '( %s -> %s e. NN )' % (ph, SQ))
    cl.leaf(SQ, 'NN0', s([sqn], 'nnnn0d', '( %s -> %s e. NN0 )' % (ph, SQ)))
    p2n = s([s([closed(w, ph, '2nn', '2 e. NN'), un, w.inst('nnexpcl')], 'syl2anc', '( %s -> %s e. NN )' % (ph, P2U)), closed(w, ph, '2nn', '2 e. NN'), w.inst('nnaddcl')], 'syl2anc',
            '( %s -> ( %s + 2 ) e. NN )' % (ph, P2U))
    e0n = s([sqn, p2n, w.inst('nnmulcl')], 'syl2anc', '( %s -> %s e. NN )' % (ph, E0_))
    cl.leaf(E0_, 'NN0', s([e0n], 'nnnn0d', '( %s -> %s e. NN0 )' % (ph, E0_)))
    wpn = s([weq, cl.mem("( %s x. U' )" % E0_, 'NN0')], 'eqeltrd', "( %s -> W' e. NN0 )" % ph)
    cl.leaf("W'", 'NN0', wpn)
    # U' <_ W' : E0 >= 1
    e01 = s([e0n, w.inst('nnge1')], 'syl', '( %s -> 1 <_ %s )' % (ph, E0_))
    uw = s([s([s([cl.mem("U'", 'RR'), cl.mem(E0_, 'RR')], 'jca', "( %s -> ( U' e. RR /\\ %s e. RR ) )" % (ph, E0_)), s([cl.ge0("U'"), e01], 'jca', "( %s -> ( 0 <_ U' /\\ 1 <_ %s ) )" % (ph, E0_))],
              'jca', "( %s -> ( ( U' e. RR /\\ %s e. RR ) /\\ ( 0 <_ U' /\\ 1 <_ %s ) ) )" % (ph, E0_, E0_)), w.inst('lemulge12')], 'syl', "( %s -> U' <_ ( %s x. U' ) )" % (ph, E0_))
    uw = s([uw, s([weq], 'eqcomd', "( %s -> ( %s x. U' ) = W' )" % (ph, E0_))], 'breqtrd', "( %s -> U' <_ W' )" % ph)
    # tmblin at X0 : C ( X0 + 2 ) <_ TMB X0 = U'
    def lin_tmb(C_):
        cn = closed(w, ph, '%snn0' % C_ if C_ != '1' else '1nn0', '%s e. NN0' % C_)
        from num import le_nat
        le = s([le_nat(w, int(C_), 64)], 'a1i', '( %s -> %s <_ ; 6 4 )' % (ph, C_))
        st = s([x0n, cn, le, w.inst('tmblin')], 'syl3anc', '( %s -> ( %s x. ( %s + 2 ) ) <_ ( TMB ` %s ) )' % (ph, C_, X0, X0))
        return s([st, s([ueq], 'eqcomd', "( %s -> ( TMB ` %s ) = U' )" % (ph, X0))], 'breqtrd', "( %s -> ( %s x. ( %s + 2 ) ) <_ U' )" % (ph, C_, X0))
    t1 = lin_tmb('1')
    t2 = lin_tmb('2')
    # the monomials of X0 (products=True: lin expands X0 in the atoms U B' 2^U)
    UBp = "( U x. B' )"
    PBp = "( %s x. B' )" % P2U
    UB = '( U x. B )'
    hy0 = [cl.ge0(UBp), cl.ge0(PBp), cl.ge0("B'"), cl.ge0('U')]
    # B' bounds
    hyB = [cl.ge0('B'), cl.ge0('H'), cl.ge0(UB)]
    bb1 = linarith(w, ph, [beq] + hyB, "B <_ B'", closure=cl, products=True)
    hb1 = linarith(w, ph, [beq] + hyB, "H <_ B'", closure=cl, products=True)
    sb5b = linarith(w, ph, [beq, b2] + hyB, "%s <_ B'" % SB5, closure=cl, products=True)
    ub1 = s([s([s([cl.mem('U', 'RR'), cl.mem('B', 'RR')], 'jca', '( %s -> ( U e. RR /\\ B e. RR ) )' % ph), s([cl.ge0('U'), linarith(w, ph, [b2], '1 <_ B', closure=cl)], 'jca', '( %s -> ( 0 <_ U /\\ 1 <_ B ) )' % ph)],
              'jca', '( %s -> ( ( U e. RR /\\ B e. RR ) /\\ ( 0 <_ U /\\ 1 <_ B ) ) )' % ph), w.inst('lemulge11')], 'syl', '( %s -> U <_ %s )' % (ph, UB))
    ult = linarith(w, ph, [ub1, beq] + hyB, "U < B'", closure=cl, products=True)
    # X0 lower bounds (linear in the atoms)
    def le_x0(e, hy):
        return linarith(w, ph, hy0 + hy, '%s <_ %s' % (e, X0), closure=cl, products=True)
    def tmb_le(e, hy):
        le = le_x0(e, hy)
        tmbleaf(w, ph, cl, e)
        return s([tmbmono(w, ph, cl, e, X0, le), s([ueq], 'eqcomd', "( %s -> ( TMB ` %s ) = U' )" % (ph, X0))], 'breqtrd', "( %s -> ( TMB ` %s ) <_ U' )" % (ph, e))
    def plus2_le(e, hy):
        le = le_x0(e, hy)
        return linarith(w, ph, [le, t1], "( %s + 2 ) <_ U'" % e, closure=cl, products=True)
    u8 = linarith(w, ph, [t1] + hy0, "8 <_ U'", closure=cl, products=True)
    b12 = plus2_le("B'", [])
    b2u = plus2_le('B', [bb1])
    h2u = plus2_le('H', [hb1])
    tb1 = tmb_le("B'", [])
    h24 = linarith(w, ph, [t2, hb1] + hy0, "( ( 2 x. H ) + 4 ) <_ U'", closure=cl, products=True)
    csc = tmb_le('( ( 3 x. ( B + H ) ) + 8 )', [bb1, hb1])
    ubb = P.mul_le2(w, ph, cl, 'U', 'B', "B'", bb1)
    cst = tmb_le('( ( ( ; 1 5 x. ( U + 1 ) ) x. B ) + ; 4 6 )', [ubb, bb1])
    exx = tmb_le(EXXU, [])
    vx = tmb_le('( ( 4 x. %s ) + 6 )' % VXU, [])
    npu2 = plus2_le(NPU, [])
    tnpu = tmb_le(NPU, [])
    hb3 = tmb_le("( ( ( ( ; 4 8 x. ( U + 1 ) ) x. ( B' + B' ) ) + ( 4 x. U ) ) + ; ; 1 0 2 )", [])
    # ( 2 ^ U + 2 ) U' <_ E0 U' = W'
    sq1 = s([sqn, w.inst('nnge1')], 'syl', '( %s -> 1 <_ %s )' % (ph, SQ))
    p2e = s([s([s([cl.mem('( %s + 2 )' % P2U, 'RR'), cl.mem(SQ, 'RR')], 'jca', '( %s -> ( ( %s + 2 ) e. RR /\\ %s e. RR ) )' % (ph, P2U, SQ)),
                s([cl.ge0('( %s + 2 )' % P2U), sq1], 'jca', '( %s -> ( 0 <_ ( %s + 2 ) /\\ 1 <_ %s ) )' % (ph, P2U, SQ))], 'jca',
               '( %s -> ( ( ( %s + 2 ) e. RR /\\ %s e. RR ) /\\ ( 0 <_ ( %s + 2 ) /\\ 1 <_ %s ) ) )' % (ph, P2U, SQ, P2U, SQ)), w.inst('lemulge12')], 'syl',
            '( %s -> ( %s + 2 ) <_ ( %s x. ( %s + 2 ) ) )' % (ph, P2U, SQ, P2U))
    p2w = s([lemul1a(w, ph, cl, '( %s + 2 )' % P2U, E0_, "U'", p2e), s([weq], 'eqcomd', "( %s -> ( %s x. U' ) = W' )" % (ph, E0_))], 'breqtrd',
            "( %s -> ( ( %s + 2 ) x. U' ) <_ W'" % (ph, P2U) + ' )')
    leaf = {"U' e. NN0": upn, "W' e. NN0": wpn, "U' <_ W'": uw, "8 <_ U'": u8, "( B' + 2 ) <_ U'": b12, "B <_ B'": bb1, "H <_ B'": hb1, "U < B'": ult,
            "( TMB ` B' ) <_ U'": tb1, "B' e. NN0": b1n, "%s <_ B'" % SB5: sb5b, "( ( 2 x. H ) + 4 ) <_ U'": h24, "%s <_ U'" % CSC_: csc, "%s <_ U'" % CST_: cst,
            "( ( %s + 2 ) x. U' ) <_ W'" % P2U: p2w, "( TMB ` %s ) <_ U'" % EXXU: exx, "( TMB ` ( ( 4 x. %s ) + 6 ) ) <_ U'" % VXU: vx,
            "( %s + 2 ) <_ U'" % NPU: npu2, "( TMB ` %s ) <_ U'" % NPU: tnpu, HB3U: hb3, "( B + 2 ) <_ U'": b2u, "( H + 2 ) <_ U'": h2u}
    st = bld_tree(w, ph, C_U0, lambda t: leaf[t])
    qed13(w, st, lab)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
