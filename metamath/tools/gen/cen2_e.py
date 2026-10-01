"""Sortie CEN2: per-character and per-pair series bounds in the family letters (cen2pt, cen2one, cen2two; Lean Census
hbound1, hbound3, hbound4 with the log bounds h6-h11)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from cen2lib import *
from cl import split_imp, Closure, lift
from c9lib import top_and
from lin import linarith, nlinarith

only = sys.argv[1:]


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


def gen_pt():
    w = W('cen2pt', 'The weight ` Lam ( k ) k ^ - ( 1 + 3 D ) ` is a nonnegative real and ` chi ( k ) k ^ - i T ` is complex.')
    A0, C0 = split_imp(S['cen2pt'])
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    nx = s([], 'simpl', '( N e. NN /\\ X e. ( Base ` ( DChr ` N ) ) )')
    kn = s([], 'simpr1', 'k e. NN'); tr = s([], 'simpr2', 'T e. RR'); dr = s([], 'simpr3', 'D e. RR')
    L = '( Lam ` k )'
    lr = s([kn, w.inst('vmacl')], 'syl', '%s e. RR' % L); l0 = s([kn, w.inst('vmage0')], 'syl', '0 <_ %s' % L)
    c = Closure(w, A0, {'k': ('NN', kn), 'D': ('RR', dr), 'T': ('RR', tr), L: [('RR', lr), ('ge0', l0)]})
    PW = '( k ^c -u ( 1 + ( 3 x. D ) ) )'
    pw = s([c.mem('k', 'RR+'), c.mem('-u ( 1 + ( 3 x. D ) )', 'RR')], 'rpcxpcld', '%s e. RR+' % PW)
    awr = s([lr, s([pw], 'rpred', '%s e. RR' % PW)], 'remulcld', '%s e. RR' % AW())
    aw0 = s([lr, s([pw], 'rpred', '%s e. RR' % PW), l0, s([pw], 'rpge0d', '0 <_ %s' % PW)], 'mulge0d', '0 <_ %s' % AW())
    CH = CHV('k'); TT = TW('T')
    ch = s([nx, s([kn], 'nnzd', 'k e. ZZ'), w.inst('cen2chv')], 'syl2anc', '( %s e. CC /\\ ( abs ` %s ) <_ 1 )' % (CH, CH))
    tw = s([kn, tr, w.inst('cen2tw')], 'syl2anc', '( %s e. CC /\\ ( abs ` %s ) = 1 )' % (TT, TT))
    vc = s([s([ch], 'simpld', '%s e. CC' % CH), s([tw], 'simpld', '%s e. CC' % TT)], 'mulcld', '%s e. CC' % VT('N', 'X', 'T'))
    w.qed([s([awr, aw0], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (AW(), AW())), vc], 'jca', S['cen2pt'])
    return run(w)


def hp0(w, ctx, P, pc, p0):
    """( ctx -> P e. HP0 ) from P e. CC and 0 < Re P"""
    HP = "( `' Re \" ( 0 (,) +oo ) )"
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (ctx, f))
    fn = w.s([w.s([], 'ref', 'Re : CC --> RR')], 'ffn', 'Re Fn CC') if False else w.s([w.s([], 'ref', 'Re : CC --> RR'), w.inst('ffn')], 'ax-mp', 'Re Fn CC')
    ep = w.s([fn, w.inst('elpreima')], 'ax-mp', "( %s e. %s <-> ( %s e. CC /\\ ( Re ` %s ) e. ( 0 (,) +oo ) ) )" % (P, HP, P, P))
    eo = w.s([w.s([], '0xr', '0 e. RR*'), w.inst('elioopnf')], 'ax-mp', '( ( Re ` %s ) e. ( 0 (,) +oo ) <-> ( ( Re ` %s ) e. RR /\\ 0 < ( Re ` %s ) ) )' % (P, P, P))
    rr = s([pc], 'recld', '( Re ` %s ) e. RR' % P)
    io = s([s([rr, p0], 'jca', '( ( Re ` %s ) e. RR /\\ 0 < ( Re ` %s ) )' % (P, P)), s([eo], 'a1i', '( ( Re ` %s ) e. ( 0 (,) +oo ) <-> ( ( Re ` %s ) e. RR /\\ 0 < ( Re ` %s ) ) )' % (P, P, P))],
           'mpbird', '( Re ` %s ) e. ( 0 (,) +oo )' % P)
    return s([s([pc, io], 'jca', "( %s e. CC /\\ ( Re ` %s ) e. ( 0 (,) +oo ) )" % (P, P)), s([ep], 'a1i', "( %s e. %s <-> ( %s e. CC /\\ ( Re ` %s ) e. ( 0 (,) +oo ) ) )" % (P, HP, P, P))],
             'mpbird', '%s e. %s' % (P, HP))


def gen_one():
    w = W('cen2one', 'The linear and diagonal series of one family member ` X ` mod ` N ` with zero ` R ` : ` sum Re ( Lam k ^ - ( 1 + 3 D ) X ( k ) k ^ - i Im R ) <_ K L - 1 / ( 4 D ) ` , ` sum Lam k ^ - ( 1 + 3 D ) | X ( k ) k ^ - i Im R | ^ 2 <_ ( 5 / 4 ) / ( 3 D ) + 5 ` , ` L = log ( Z ( V + 2 ) ) ` (Lean Census ` hbound1 ` , ` hbound3 ` ; the zero of ` DChrLF ` is a zero of the Abel series by ZC1 ~ zc1eord ).')
    A0, C0 = split_imp(S['cen2one'])
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    F = split_all(w, A0, A0, w.s([], 'id', '( %s -> %s )' % (A0, A0)))
    g = lambda f: F[f]
    nn = g('N e. NN'); n2 = g('2 <_ N'); nz = g('N <_ Z'); xd = g('X e. ( Base ` ( DChr ` N ) )'); xc = g('( N DChrCond X ) = N')
    rc = g('R e. CC'); r1 = g('R =/= 1'); rz = g('( ( N DChrLF X ) ` R ) = 0')
    lo = g('( 1 - D ) <_ ( Re ` R )'); hi = g('( Re ` R ) <_ 1'); im = g('( abs ` ( Im ` R ) ) <_ V')
    drp = g('D e. RR+'); dle = g('D <_ %s' % F140); vr = g('V e. RR'); v1 = g('1 <_ V'); zr = g('Z e. RR'); z2 = g('2 <_ Z')
    DN = '( Base ` ( DChr ` N ) )'
    nx = s([nn, xd], 'jca', '( N e. NN /\\ X e. %s )' % DN)
    ne = s([s([nn, n2], 'jca', '( N e. NN /\\ 2 <_ N )'), s([xd, xc], 'jca', '( X e. %s /\\ ( N DChrCond X ) = N )' % DN), w.inst('dchrprimne1')], 'syl2anc', 'X =/= ( 0g ` ( DChr ` N ) )')
    chi = s([nx, ne], 'jca', CHI)
    c = Closure(w, A0, {'D': ('RR+', drp), 'V': ('RR', vr), 'Z': ('RR', zr), 'N': ('NN', nn)})
    c.have('( Re ` R )', 'RR', s([rc], 'recld', '( Re ` R ) e. RR'))
    p0 = linarith(w, A0, [lo, dle], '0 < ( Re ` R )', closure=c)
    hp = hp0(w, A0, 'R', rc, p0)
    ZE = tokrep(stmt('zc1eord'), {'P': 'R'})
    za, zcn = split_imp(ZE)
    ze = s([s([chi, s([hp, r1], 'jca', top_and(za)[1])], 'jca', za), w.inst('zc1eord')], 'syl', zcn)
    lz = s([rz, s([ze], 'simprd', top_and(zcn)[1])], 'mpbid', '( %s ` R ) = 0' % LFN)
    GBA, GBC = split_imp(tokrep(S['cen2gb'], {}))
    gba = s([chi, s([drp, dle], 'jca', DDH) if False else s([drp, dle], 'jca', DDH)], 'jca', '( %s /\\ %s )' % (CHI, DDH)) if False else None
    t2 = top_and(GBA)[1]
    rest = top_and(t2)[1]
    gb = s([s([chi, s([s([drp, dle], 'jca', DDH), s([rc, lz, s([lo, hi], 'jca', '( ( 1 - D ) <_ ( Re ` R ) /\\ ( Re ` R ) <_ 1 )')], '3jca', rest)], 'jca', t2)], 'jca', GBA),
            w.inst('cen2gb')], 'syl', GBC)
    G = split_all(w, A0, GBC, gb)
    IR = '( Im ` R )'
    ir = s([rc], 'imcld', '%s e. RR' % IR)
    c.have(IR, 'RR', ir)
    AI = '( abs ` %s )' % IR
    c.have(AI, 'RR', s([ir], 'recnd', '%s e. CC' % IR) and s([s([ir], 'recnd', '%s e. CC' % IR)], 'abscld', '%s e. RR' % AI))
    ai0 = s([s([ir], 'recnd', '%s e. CC' % IR)], 'absge0d', '0 <_ %s' % AI)
    c.have(AI, 'ge0', ai0)
    X1 = '( %s + 2 )' % AI; X2 = '( V + 2 )'
    n0 = c.ge0('N')
    le1 = s([c.mem('N', 'RR'), zr, c.mem(X1, 'RR'), c.mem(X2, 'RR'), n0, c.ge0(X1), nz, linarith(w, A0, [im], '%s <_ %s' % (X1, X2), closure=c)], 'lemul12ad',
            '( N x. %s ) <_ ( Z x. %s )' % (X1, X2))
    AA = '( N x. %s )' % X1; BB = '( Z x. %s )' % X2
    z0 = linarith(w, A0, [z2], '0 < Z', closure=c)
    c.have('Z', 'gt0', z0)
    v0 = linarith(w, A0, [v1], '0 < %s' % X2, closure=c)
    c.have(X2, 'gt0', v0)
    lg = s([le1, s([c.mem(AA, 'RR+'), c.mem(BB, 'RR+')], 'logled', '( %s <_ %s <-> ( log ` %s ) <_ ( log ` %s ) )' % (AA, BB, AA, BB))], 'mpbid', '( log ` %s ) <_ ( log ` %s )' % (AA, BB))
    kl = s([c.mem('( log ` %s )' % AA, 'RR'), c.mem('( log ` %s )' % BB, 'RR'), c.mem(KLAN, 'RR'), c.ge0(KLAN), lg], 'lemul2ad', '( %s x. ( log ` %s ) ) <_ ( %s x. ( log ` %s ) )' % (KLAN, AA, KLAN, BB))
    B1 = split_imp(S['cen2one'])[1]
    (bpart, cpart) = top_and(B1)
    bcv, bsec = top_and(bpart)
    bre, ble = top_and(bsec)
    SB = bre.rsplit(' e. RR', 1)[0]
    oldle = [f for f in G if f.startswith(SB + ' <_ ')][0]
    c.have(SB, 'RR', G[bre])
    c.atom('( log ` %s )' % AA); c.atom('( log ` %s )' % BB); c.atom('( 1 / ( 4 x. D ) )')
    nle = linarith(w, A0, [G[oldle], kl], ble, closure=c)
    GC = tokrep(split_imp(S['cen2gc'])[1], {'T': IR})
    gc = s([nx, s([ir, s([drp, dle], 'jca', DDH)], 'jca', '( %s e. RR /\\ %s )' % (IR, DDH)), w.inst('cen2gc')], 'syl2anc', GC)
    cp = s([gc], 'simprd', top_and(GC)[1])
    w.qed([s([G[bcv], s([G[bre], nle], 'jca', bsec)], 'jca', bpart), cp], 'jca', S['cen2one'])
    return run(w)


def gen_two():
    w = W('cen2two', 'The cross series of two distinct family members: ` sum Re ( Lam k ^ - ( 1 + 3 D ) X ( k ) k ^ - i Im R * ( Y ( k ) k ^ - i Im Q ) ) <_ K ( 2 L ) ` , ` L = log ( Z ( V + 2 ) ) ` (Lean Census ` hbound4 ` with ` h6 ` - ` h11 ` : ` N M ( | Im R - Im Q | + 2 ) <_ ( Z ( V + 2 ) ) ^ 2 ` ).')
    A0, C0 = split_imp(S['cen2two'])
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    F = split_all(w, A0, A0, w.s([], 'id', '( %s -> %s )' % (A0, A0)))
    g = lambda f: F[f]
    nn = g('N e. NN'); nz = g('N <_ Z'); xd = g('X e. ( Base ` ( DChr ` N ) )'); xc = g('( N DChrCond X ) = N')
    mn = g('M e. NN'); mz = g('M <_ Z'); yd = g('Y e. ( Base ` ( DChr ` M ) )'); yc = g('( M DChrCond Y ) = M')
    rc = g('R e. CC'); qc = g('Q e. CC'); imr = g('( abs ` ( Im ` R ) ) <_ V'); imq = g('( abs ` ( Im ` Q ) ) <_ V'); xy = g('X =/= Y')
    drp = g('D e. RR+'); dle = g('D <_ %s' % F140); vr = g('V e. RR'); v1 = g('1 <_ V'); zr = g('Z e. RR'); z2 = g('2 <_ Z')
    IR = '( Im ` R )'; IQ = '( Im ` Q )'
    ir = s([rc], 'imcld', '%s e. RR' % IR); iq = s([qc], 'imcld', '%s e. RR' % IQ)
    PR = tokrep(split_imp(S['cen2gd'])[0], {'T': IR, 'U': IQ})
    DN = '( Base ` ( DChr ` N ) )'; DM = '( Base ` ( DChr ` M ) )'
    p1 = s([s([nn, mn], 'jca', '( N e. NN /\\ M e. NN )'),
            s([s([xd, xc], 'jca', '( X e. %s /\\ ( N DChrCond X ) = N )' % DN), s([yd, yc], 'jca', '( Y e. %s /\\ ( M DChrCond Y ) = M )' % DM)], 'jca',
              top_and(top_and(PR)[0])[1]), xy], '3jca', top_and(PR)[0])
    p2 = s([s([ir, iq], 'jca', '( %s e. RR /\\ %s e. RR )' % (IR, IQ)), s([drp, dle], 'jca', DDH)], 'jca', top_and(PR)[1])
    GD = tokrep(split_imp(S['cen2gd'])[1], {'T': IR, 'U': IQ})
    gd = s([s([p1, p2], 'jca', PR), w.inst('cen2gd')], 'syl', GD)
    G = split_all(w, A0, GD, gd)
    c = Closure(w, A0, {'D': ('RR+', drp), 'V': ('RR', vr), 'Z': ('RR', zr), 'N': ('NN', nn), 'M': ('NN', mn), IR: ('RR', ir), IQ: ('RR', iq)})
    TU = '( %s - %s )' % (IR, IQ)
    AT = '( abs ` %s )' % TU
    tuc = c.mem(TU, 'CC')
    c.have(AT, 'RR', s([tuc], 'abscld', '%s e. RR' % AT)); c.have(AT, 'ge0', s([tuc], 'absge0d', '0 <_ %s' % AT))
    ARr = '( abs ` %s )' % IR; AQr = '( abs ` %s )' % IQ
    c.have(ARr, 'RR', s([c.mem(IR, 'CC')], 'abscld', '%s e. RR' % ARr)); c.have(AQr, 'RR', s([c.mem(IQ, 'CC')], 'abscld', '%s e. RR' % AQr))
    tri = s([c.mem(IR, 'CC'), c.mem(IQ, 'CC')], 'abs2dif2d', '%s <_ ( %s + %s )' % (AT, ARr, AQr))
    X1 = '( %s + 2 )' % AT; V2 = '( V + 2 )'; VV = '( %s x. %s )' % (V2, V2)
    x1le = nlinarith(w, A0, [tri, imr, imq, v1], '%s <_ %s' % (X1, VV), closure=c)
    NM = '( N x. M )'; ZZ_ = '( Z x. Z )'
    nmle = s([c.mem('N', 'RR'), zr, c.mem('M', 'RR'), zr, c.ge0('N'), c.ge0('M'), nz, mz], 'lemul12ad', '%s <_ %s' % (NM, ZZ_))
    AA = '( %s x. %s )' % (NM, X1); BB = '( %s x. %s )' % (ZZ_, VV)
    le1 = s([c.mem(NM, 'RR'), c.mem(ZZ_, 'RR'), c.mem(X1, 'RR'), c.mem(VV, 'RR'), c.ge0(NM), c.ge0(X1), nmle, x1le], 'lemul12ad', '%s <_ %s' % (AA, BB))
    WW = '( Z x. %s )' % V2
    z0 = linarith(w, A0, [z2], '0 < Z', closure=c); c.have('Z', 'gt0', z0)
    v0 = linarith(w, A0, [v1], '0 < %s' % V2, closure=c); c.have(V2, 'gt0', v0)
    m4 = s([c.mem('Z', 'CC'), c.mem('Z', 'CC'), c.mem(V2, 'CC'), c.mem(V2, 'CC')], 'mul4d', '( %s x. %s ) = ( %s x. %s )' % (ZZ_, VV, WW, WW))
    le2 = s([le1, m4], 'breqtrd', '%s <_ ( %s x. %s )' % (AA, WW, WW))
    W2 = '( %s x. %s )' % (WW, WW)
    lg = s([le2, s([c.mem(AA, 'RR+'), c.mem(W2, 'RR+')], 'logled', '( %s <_ %s <-> ( log ` %s ) <_ ( log ` %s ) )' % (AA, W2, AA, W2))], 'mpbid', '( log ` %s ) <_ ( log ` %s )' % (AA, W2))
    lm = s([c.mem(WW, 'RR+'), c.mem(WW, 'RR+')], 'relogmuld', '( log ` %s ) = ( ( log ` %s ) + ( log ` %s ) )' % (W2, WW, WW))
    kl = s([c.mem('( log ` %s )' % AA, 'RR'), c.mem('( log ` %s )' % W2, 'RR'), c.mem(KLAN, 'RR'), c.ge0(KLAN), lg], 'lemul2ad', '( %s x. ( log ` %s ) ) <_ ( %s x. ( log ` %s ) )' % (KLAN, AA, KLAN, W2))
    C1 = split_imp(S['cen2two'])[1]
    ecv, esec = top_and(C1)
    ere, ele = top_and(esec)
    SE = ere.rsplit(' e. RR', 1)[0]
    oldle = [f for f in G if f.startswith(SE + ' <_ ')][0]
    for a_ in ('( log ` %s )' % AA, '( log ` %s )' % W2, '( log ` %s )' % WW):
        c.atom(a_)
    c.have(SE, 'RR', G[ere])
    nle = linarith(w, A0, [G[oldle], kl, lm], ele, closure=c)
    w.qed([G[ecv], s([G[ere], nle], 'jca', esec)], 'jca', S['cen2two'])
    return run(w)


if __name__ == '__main__':
    gen_pt()
    gen_one()
    gen_two()
