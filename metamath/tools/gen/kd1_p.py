"""Sortie KD1: a square of half-side in [1/3, 2/5] whose frame misses a finite set (kdfrm)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from kd1lib import *
from cl import formula_of, lift
from lin import linarith, lineq
from kd1_e import reim

only = sys.argv[1:]


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


def gen_frm():
    w = W('kdfrm', 'Among the squares ` SQ ( P , r ) ` , ` 1 / 3 <_ r <_ 2 / 5 ` , one has a frame missing a given finite set ` Z ` (ZC1 ` gappt ` on the rescaled distances).')
    A0 = S['kdfrm'].split(' -> E. r')[0][2:]
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    zf = s([], 'simp1', 'Z e. Fin'); zcc = s([], 'simp2', 'Z C_ CC'); pc = s([], 'simp3', 'P e. CC')
    R3 = '( 1 / 3 )'
    VR = lambda u: '( ; 1 5 x. ( ( abs ` ( Re ` ( %s - P ) ) ) - %s ) )' % (u, R3)
    VI = lambda u: '( ; 1 5 x. ( ( abs ` ( Im ` ( %s - P ) ) ) - %s ) )' % (u, R3)
    G1 = '( x e. Z |-> %s )' % VR('x'); G2 = '( x e. Z |-> %s )' % VI('x')
    G = '( ran %s u. ran %s )' % (G1, G2)
    Az = '( %s /\\ x e. Z )' % A0
    t = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Az, f))
    uc = t([lift(w, zcc, Az), t([], 'simpr', 'x e. Z')], 'sseldd', 'x e. CC')
    up = t([uc, lift(w, pc, Az)], 'subcld', '( x - P ) e. CC')
    c = Closure(w, Az, {'( abs ` ( Re ` ( x - P ) ) )': ('RR', t([t([up], 'recld', '( Re ` ( x - P ) ) e. RR')], 'recnd', '( Re ` ( x - P ) ) e. CC') and
                                                          t([t([t([up], 'recld', '( Re ` ( x - P ) ) e. RR')], 'recnd', '( Re ` ( x - P ) ) e. CC')], 'abscld', '( abs ` ( Re ` ( x - P ) ) ) e. RR')),
                        '( abs ` ( Im ` ( x - P ) ) )': ('RR', t([t([t([up], 'imcld', '( Im ` ( x - P ) ) e. RR')], 'recnd', '( Im ` ( x - P ) ) e. CC')], 'abscld', '( abs ` ( Im ` ( x - P ) ) ) e. RR'))})
    c.atom('( abs ` ( Re ` ( x - P ) ) )'); c.atom('( abs ` ( Im ` ( x - P ) ) )')
    vr = c.mem(VR('x'), 'RR'); vi = c.mem(VI('x'), 'RR')
    f1 = s([vr], 'fmptd', '%s : Z --> RR' % G1); f2 = s([vi], 'fmptd', '%s : Z --> RR' % G2)
    gfin = s([s([s([zf, w.inst('mptfi')], 'syl', '%s e. Fin' % G1), w.inst('rnfi')], 'syl', 'ran %s e. Fin' % G1),
              s([s([zf, w.inst('mptfi')], 'syl', '%s e. Fin' % G2), w.inst('rnfi')], 'syl', 'ran %s e. Fin' % G2), w.inst('unfi')], 'syl2anc', '%s e. Fin' % G)
    gss = s([s([f1, w.inst('frn')], 'syl', 'ran %s C_ RR' % G1), s([f2, w.inst('frn')], 'syl', 'ran %s C_ RR' % G2)], 'unssd', '%s C_ RR' % G)
    GAP = '( 1 / ( 2 x. ( ( # ` %s ) + 1 ) ) )' % G
    gp = s([s([gfin, gss], 'jca', '( %s e. Fin /\\ %s C_ RR )' % (G, G)), w.s([], '0red', '( %s -> 0 e. RR )' % A0), w.inst('gappt')], 'syl2anc',
           'E. t e. ( 0 [,] ( 0 + 1 ) ) A. g e. %s %s <_ ( abs ` ( t - g ) )' % (G, GAP))
    Bt = '( ( %s /\\ t e. ( 0 [,] ( 0 + 1 ) ) ) /\\ A. g e. %s %s <_ ( abs ` ( t - g ) ) )' % (A0, G, GAP)
    b = lambda h, r_, f: w.s(h, r_, '( %s -> %s )' % (Bt, f))
    LB = lambda st: lift(w, st, Bt)
    ti = b([], 'simplr', 't e. ( 0 [,] ( 0 + 1 ) )')
    tall = b([], 'simpr', 'A. g e. %s %s <_ ( abs ` ( t - g ) )' % (G, GAP))
    z0 = w.s([], '0red', '( %s -> 0 e. RR )' % Bt)
    o1 = b([z0, w.s([], '1red', '( %s -> 1 e. RR )' % Bt)], 'readdcld', '( 0 + 1 ) e. RR')
    te = b([ti, b([z0, o1, w.inst('elicc2')], 'syl2anc', '( t e. ( 0 [,] ( 0 + 1 ) ) <-> ( t e. RR /\\ 0 <_ t /\\ t <_ ( 0 + 1 ) ) )')], 'mpbid', '( t e. RR /\\ 0 <_ t /\\ t <_ ( 0 + 1 ) )')
    tr = b([te], 'simp1d', 't e. RR'); t0 = b([te], 'simp2d', '0 <_ t'); t1 = b([te], 'simp3d', 't <_ ( 0 + 1 )')
    R = '( ( 1 / 3 ) + ( t / ; 1 5 ) )'
    cb = Closure(w, Bt, {'t': ('RR', tr)})
    rr = cb.mem(R, 'RR')
    r1 = linarith(w, Bt, [t0], '( 1 / 3 ) <_ %s' % R, closure=cb)
    r2 = linarith(w, Bt, [t1], '%s <_ ( 2 / 5 )' % R, closure=cb)
    rin = b([rr, r1, r2, b([cb.mem('( 1 / 3 )', 'RR'), cb.mem('( 2 / 5 )', 'RR'), w.inst('elicc2')], 'syl2anc', '( %s e. ( ( 1 / 3 ) [,] ( 2 / 5 ) ) <-> ( %s e. RR /\\ ( 1 / 3 ) <_ %s /\\ %s <_ ( 2 / 5 ) ) )' % (R, R, R, R))],
            'T.', 'T.') if False else b([b([rr, r1, r2], '3jca', '( %s e. RR /\\ ( 1 / 3 ) <_ %s /\\ %s <_ ( 2 / 5 ) )' % (R, R, R)),
                                        b([cb.mem('( 1 / 3 )', 'RR'), cb.mem('( 2 / 5 )', 'RR'), w.inst('elicc2')], 'syl2anc', '( %s e. ( ( 1 / 3 ) [,] ( 2 / 5 ) ) <-> ( %s e. RR /\\ ( 1 / 3 ) <_ %s /\\ %s <_ ( 2 / 5 ) ) )' % (R, R, R, R))],
                                       'mpbird', '%s e. ( ( 1 / 3 ) [,] ( 2 / 5 ) )' % R)
    r0 = linarith(w, Bt, [t0], '0 < %s' % R, closure=cb)
    # -. t e. G
    hn = b([b([LB(gfin), w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % G), w.inst('nn0p1nn')], 'syl', '( ( # ` %s ) + 1 ) e. NN' % G)
    gpos = b([b([w.s([w.s([], '2rp', '2 e. RR+')], 'a1i', '( %s -> 2 e. RR+ )' % Bt), b([hn], 'nnrpd', '( ( # ` %s ) + 1 ) e. RR+' % G)], 'rpmulcld', '( 2 x. ( ( # ` %s ) + 1 ) ) e. RR+' % G)],
             'rpreccld', '%s e. RR+' % GAP)
    cg = w.s([w.s([w.s([], 'oveq2', '( g = t -> ( t - g ) = ( t - t ) )')], 'fveq2d', '( g = t -> ( abs ` ( t - g ) ) = ( abs ` ( t - t ) ) )')], 'breq2d',
             '( g = t -> ( %s <_ ( abs ` ( t - g ) ) <-> %s <_ ( abs ` ( t - t ) ) ) )' % (GAP, GAP))
    tt0 = b([b([b([tr], 'recnd', 't e. CC')], 'subidd', '( t - t ) = 0')], 'fveq2d', '( abs ` ( t - t ) ) = ( abs ` 0 )')
    tt1 = b([tt0, w.s([w.s([], 'abs0', '( abs ` 0 ) = 0')], 'a1i', '( %s -> ( abs ` 0 ) = 0 )' % Bt)], 'eqtrd', '( abs ` ( t - t ) ) = 0')
    # ( t e. G -> GAP <_ 0 ), but 0 < GAP
    rs1 = w.s([w.s([cg], 'rspcv', '( t e. %s -> ( A. g e. %s %s <_ ( abs ` ( t - g ) ) -> %s <_ ( abs ` ( t - t ) ) ) )' % (G, G, GAP, GAP))], 'com12',
              '( A. g e. %s %s <_ ( abs ` ( t - g ) ) -> ( t e. %s -> %s <_ ( abs ` ( t - t ) ) ) )' % (G, GAP, G, GAP))
    rs2 = b([tall, rs1], 'syl', '( t e. %s -> %s <_ ( abs ` ( t - t ) ) )' % (G, GAP))
    lt0 = b([w.s([], '0red', '( %s -> 0 e. RR )' % Bt), b([gpos], 'rpred', '%s e. RR' % GAP)], 'ltnled', '( 0 < %s <-> -. %s <_ 0 )' % (GAP, GAP))
    ngl = b([b([gpos], 'rpgt0d', '0 < %s' % GAP), lt0], 'T.', 'T.') if False else b([b([gpos], 'rpgt0d', '0 < %s' % GAP), lt0], 'mpbid', '-. %s <_ 0' % GAP)
    rs3 = b([rs2, b([tt1], 'breq2d', '( %s <_ ( abs ` ( t - t ) ) <-> %s <_ 0 )' % (GAP, GAP))], 'T.', 'T.') if False else \
        b([rs2, w.s([b([tt1], 'breq2d', '( %s <_ ( abs ` ( t - t ) ) <-> %s <_ 0 )' % (GAP, GAP))], 'biimpd', '( %s -> ( %s <_ ( abs ` ( t - t ) ) -> %s <_ 0 ) )' % (Bt, GAP, GAP))], 'syld', '( t e. %s -> %s <_ 0 )' % (G, GAP))
    ntG = b([rs3, ngl], 'mtod', '-. t e. %s' % G)
    # ---- the frame of SQ(P,R)
    rp = b([rr, r0], 'elrpd', '%s e. RR+' % R)
    from kd1_c import sqctx
    A_, B_ = QLO('P', R), QHI('P', R)
    FR = FSQ('P', R)
    # corners in CC and order (sqctx is written for the radius letter R: substitute)
    def reim2(ante, pc_, rr_):
        a = lambda h, r_, f: w.s(h, r_, '( %s -> %s )' % (ante, f))
        RI_ = '( %s + ( _i x. %s ) )' % (R, R)
        rc = a([rr_], 'recnd', '%s e. CC' % R)
        ic = w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % ante)
        ric = a([rc, a([ic, rc], 'mulcld', '( _i x. %s ) e. CC' % R)], 'addcld', '%s e. CC' % RI_)
        crr = a([rr_, rr_, w.inst('crre')], 'syl2anc', '( Re ` %s ) = %s' % (RI_, R))
        cri = a([rr_, rr_, w.inst('crim')], 'syl2anc', '( Im ` %s ) = %s' % (RI_, R))
        out = {'ric': ric}
        for nm, op, lab, part, cr in (('ReA', '-', 'resub', 'Re', crr), ('ReB', '+', 'readd', 'Re', crr), ('ImA', '-', 'imsub', 'Im', cri), ('ImB', '+', 'imadd', 'Im', cri)):
            X = A_ if op == '-' else B_
            e1 = a([pc_, ric, w.inst(lab)], 'syl2anc', '( %s ` %s ) = ( ( %s ` P ) %s ( %s ` %s ) )' % (part, X, part, op, part, RI_))
            e2 = a([cr], 'oveq2d', '( ( %s ` P ) %s ( %s ` %s ) ) = ( ( %s ` P ) %s %s )' % (part, op, part, RI_, part, op, R))
            out[nm] = a([e1, e2], 'eqtrd', '( %s ` %s ) = ( ( %s ` P ) %s %s )' % (part, X, part, op, R))
        return out
    pcb = LB(pc)
    ri = reim2(Bt, pcb, rr)
    ac = b([pcb, ri['ric']], 'subcld', '%s e. CC' % A_); bc = b([pcb, ri['ric']], 'addcld', '%s e. CC' % B_)
    cbr = Closure(w, Bt, {'t': ('RR', tr), '( Re ` P )': ('RR', b([pcb], 'recld', '( Re ` P ) e. RR')), '( Im ` P )': ('RR', b([pcb], 'imcld', '( Im ` P ) e. RR')),
                          '( Re ` %s )' % A_: ('RR', b([ac], 'recld', '( Re ` %s ) e. RR' % A_)), '( Re ` %s )' % B_: ('RR', b([bc], 'recld', '( Re ` %s ) e. RR' % B_)),
                          '( Im ` %s )' % A_: ('RR', b([ac], 'imcld', '( Im ` %s ) e. RR' % A_)), '( Im ` %s )' % B_: ('RR', b([bc], 'imcld', '( Im ` %s ) e. RR' % B_))})
    for e_ in ('( Re ` P )', '( Im ` P )', '( Re ` %s )' % A_, '( Re ` %s )' % B_, '( Im ` %s )' % A_, '( Im ` %s )' % B_):
        cbr.atom(e_)
    ore = linarith(w, Bt, [ri['ReA'], ri['ReB'], r0], '( Re ` %s ) <_ ( Re ` %s )' % (A_, B_), closure=cbr)
    oim = linarith(w, Bt, [ri['ImA'], ri['ImB'], r0], '( Im ` %s ) <_ ( Im ` %s )' % (A_, B_), closure=cbr)
    DJ = '( ( ( Re ` u ) = ( Re ` %s ) \\/ ( Re ` u ) = ( Re ` %s ) ) \\/ ( ( Im ` u ) = ( Im ` %s ) \\/ ( Im ` u ) = ( Im ` %s ) ) )' % (A_, B_, A_, B_)
    cre = b([b([ac, bc], 'jca', '( %s e. CC /\\ %s e. CC )' % (A_, B_)), b([ore, oim], 'jca', '( ( Re ` %s ) <_ ( Re ` %s ) /\\ ( Im ` %s ) <_ ( Im ` %s ) )' % (A_, B_, A_, B_)), w.inst('crectfre')],
            'syl2anc', 'A. u e. %s %s' % (FR, DJ))
    Bu = '( %s /\\ u e. %s )' % (Bt, FR)
    Cz = '( %s /\\ u e. Z )' % Bu
    dj = w.s([w.s([cre], 'r19.21bi', '( %s -> %s )' % (Bu, DJ))], 'adantr', '( %s -> %s )' % (Cz, DJ))
    def case(part, corner, sign):
        """( Cz -> ( ( part ` u ) = ( part ` corner ) -> t e. G ) )"""
        H_ = '( ( %s ` u ) = ( %s ` %s ) )' % (part, part, corner)
        Ch = '( %s /\\ ( %s ` u ) = ( %s ` %s ) )' % (Cz, part, part, corner)
        a = lambda h, r_, f: w.s(h, r_, '( %s -> %s )' % (Ch, f))
        L = lambda st: lift(w, st, Ch)
        hu = a([], 'simpr', '( %s ` u ) = ( %s ` %s )' % (part, part, corner))
        uz = w.s([w.s([], 'simpr', '( %s -> u e. Z )' % Cz)], 'adantr', '( %s -> u e. Z )' % Ch)
        ucc = a([L(zcc), uz], 'sseldd', 'u e. CC')
        pcc = L(pc)
        rsub = a([ucc, pcc], 'resubd' if part == 'Re' else 'imsubd', '( %s ` ( u - P ) ) = ( ( %s ` u ) - ( %s ` P ) )' % (part, part, part))
        key = {('Re', A_): 'ReA', ('Re', B_): 'ReB', ('Im', A_): 'ImA', ('Im', B_): 'ImB'}[(part, corner)]
        cor = L(ri[key])
        cc = Closure(w, Ch, {'t': ('RR', L(tr)), '( %s ` u )' % part: ('RR', a([ucc], 'recld' if part == 'Re' else 'imcld', '( %s ` u ) e. RR' % part)),
                             '( %s ` P )' % part: ('RR', a([pcc], 'recld' if part == 'Re' else 'imcld', '( %s ` P ) e. RR' % part)),
                             '( %s ` %s )' % (part, corner): ('RR', a([L(ac if corner == A_ else bc)], 'recld' if part == 'Re' else 'imcld', '( %s ` %s ) e. RR' % (part, corner)))})
        for e_ in ('( %s ` u )' % part, '( %s ` P )' % part, '( %s ` %s )' % (part, corner)):
            cc.atom(e_)
        val = ('-u %s' % R) if sign < 0 else R
        dv = lineq(w, Ch, '( ( %s ` u ) - ( %s ` P ) )' % (part, part), val, hyps=[hu, cor], closure=cc)
        d2 = a([rsub, dv], 'eqtrd', '( %s ` ( u - P ) ) = %s' % (part, val))
        ab = a([d2], 'fveq2d', '( abs ` ( %s ` ( u - P ) ) ) = ( abs ` %s )' % (part, val))
        rrh = L(rr); r0h = a([L(r0), rrh] and [rrh, L(r0)], 'T.', 'T.') if False else None
        r0le = a([w.s([], '0red', '( %s -> 0 e. RR )' % Ch), L(rr), L(r0)], 'ltled', '0 <_ %s' % R)
        if sign < 0:
            ab2 = a([ab, a([a([L(rr)], 'recnd', '%s e. CC' % R)], 'absnegd', '( abs ` -u %s ) = ( abs ` %s )' % (R, R)), a([L(rr), r0le], 'absidd', '( abs ` %s ) = %s' % (R, R))], '3eqtrd',
                    '( abs ` ( %s ` ( u - P ) ) ) = %s' % (part, R))
        else:
            ab2 = a([ab, a([L(rr), r0le], 'absidd', '( abs ` %s ) = %s' % (R, R))], 'eqtrd', '( abs ` ( %s ` ( u - P ) ) ) = %s' % (part, R))
        VX = VR if part == 'Re' else VI
        GG = G1 if part == 'Re' else G2
        v1 = a([ab2], 'oveq1d', '( ( abs ` ( %s ` ( u - P ) ) ) - ( 1 / 3 ) ) = ( %s - ( 1 / 3 ) )' % (part, R))
        v2 = a([v1], 'oveq2d', '%s = ( ; 1 5 x. ( %s - ( 1 / 3 ) ) )' % (VX('u'), R))
        ct = Closure(w, Ch, {'t': ('RR', L(tr))})
        v3 = lineq(w, Ch, '( ; 1 5 x. ( %s - ( 1 / 3 ) ) )' % R, 't', closure=ct)
        tv = a([v2, v3], 'eqtrd', '%s = t' % VX('u'))
        tv2 = a([tv], 'eqcomd', 't = %s' % VX('u'))
        idx = w.s([], 'id', '( x = u -> x = u )')
        cx, nx = w.congr(VX('x'), {'x': 'u'}, 'x = u', {'x': idx})
        ceq = w.s([cx], 'eqeq2d', '( x = u -> ( t = %s <-> t = %s ) )' % (VX('x'), VX('u')))
        ex_ = a([uz, tv2, w.s([ceq], 'rspcev', '( ( u e. Z /\\ t = %s ) -> E. x e. Z t = %s )' % (VX('u'), VX('x')))], 'syl2anc', 'E. x e. Z t = %s' % VX('x'))
        tin = a([ex_, L(tr)], 'T.', 'T.') if False else w.s([w.s([], 'eqid', '%s = %s' % (GG, GG)), ex_, L(tr)], 'elrnmptd', '( %s -> t e. ran %s )' % (Ch, GG))
        tG = a([tin, w.inst('elun1' if part == 'Re' else 'elun2')], 'syl', 't e. %s' % G)
        return w.s([tG], 'ex', '( %s -> ( ( %s ` u ) = ( %s ` %s ) -> t e. %s ) )' % (Cz, part, part, corner, G))
    k1 = case('Re', A_, -1); k2 = case('Re', B_, 1); k3 = case('Im', A_, -1); k4 = case('Im', B_, 1)
    j1 = w.s([k1, k2], 'jaod', '( %s -> ( ( ( Re ` u ) = ( Re ` %s ) \\/ ( Re ` u ) = ( Re ` %s ) ) -> t e. %s ) )' % (Cz, A_, B_, G))
    j2 = w.s([k3, k4], 'jaod', '( %s -> ( ( ( Im ` u ) = ( Im ` %s ) \\/ ( Im ` u ) = ( Im ` %s ) ) -> t e. %s ) )' % (Cz, A_, B_, G))
    j3 = w.s([j1, j2], 'jaod', '( %s -> ( %s -> t e. %s ) )' % (Cz, DJ, G))
    tGz = w.s([dj, j3], 'mpd', '( %s -> t e. %s )' % (Cz, G))
    nuz = w.s([tGz, lift(w, ntG, Bu)], 'mtand', '( %s -> -. u e. Z )' % Bu)
    allu = b([nuz], 'ralrimiva', 'A. u e. %s -. u e. Z' % FR)
    idr = w.s([], 'id', '( r = %s -> r = %s )' % (R, R))
    cr_, nr_ = w.wcongr('A. u e. %s -. u e. Z' % FSQ('P', 'r'), {'r': R}, 'r = %s' % R, {'r': idr})
    assert nr_ == 'A. u e. %s -. u e. Z' % FR, nr_
    exr = b([rin, allu, w.s([cr_], 'rspcev', '( ( %s e. ( ( 1 / 3 ) [,] ( 2 / 5 ) ) /\\ A. u e. %s -. u e. Z ) -> E. r e. ( ( 1 / 3 ) [,] ( 2 / 5 ) ) A. u e. %s -. u e. Z )' % (R, FR, FSQ('P', 'r')))],
            'syl2anc', 'E. r e. ( ( 1 / 3 ) [,] ( 2 / 5 ) ) A. u e. %s -. u e. Z' % FSQ('P', 'r'))
    GOAL = 'E. r e. ( ( 1 / 3 ) [,] ( 2 / 5 ) ) A. u e. %s -. u e. Z' % FSQ('P', 'r')
    rl = w.s([w.s([exr], 'ex', '( ( %s /\\ t e. ( 0 [,] ( 0 + 1 ) ) ) -> ( A. g e. %s %s <_ ( abs ` ( t - g ) ) -> %s ) )' % (A0, G, GAP, GOAL))], 'rexlimdva',
             '( %s -> ( E. t e. ( 0 [,] ( 0 + 1 ) ) A. g e. %s %s <_ ( abs ` ( t - g ) ) -> %s ) )' % (A0, G, GAP, GOAL))
    w.qed([gp, rl], 'mpd', S['kdfrm'])
    return run(w)




if __name__ == '__main__':
    gen_frm()
