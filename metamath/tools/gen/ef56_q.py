"""Sortie EF56: Lean contour_zeta (ef6cnt): the existential eliminations around ef6core."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from ef56lib import *
from c8_o import numst
import congr as _cg
from cl import lift, Closure
import lin
lin.FASTPATH = True
from ef4_a import ic_, ptc, icc_in, icc_out
from ef4_f import c1_facts


def cbvral_rex(w, X, var, new, body):
    eq, nb = w.wcongr(body, {var: new}, '%s = %s' % (var, new), {var: w.s([], 'id', '( %s = %s -> %s = %s )' % (var, new, var, new))})
    return w.s([eq], 'cbvrexvw', '( E. %s e. %s %s <-> E. %s e. %s %s )' % (var, X, body, new, X, nb)), nb





def gen_cnt():
    w = W('ef6cnt', 'Lean ` contour_zeta ` : at the character mod 1, for ` y >_ 100 ` , ` T >_ 2 ` , ` abs ( PS + 2 pi i SC - 2 pi i y ) <_ 2 pi 1000000000 ( y log ^ 2 ( T y ) / T + y ^ ( 5 / 8 ) log ^ 2 ( T + 2 ) ) ` ( ` PS ` = ` 2 pi i ` times the Perron sum, ` SC ` the zero sum of ` zeta ` ; the heights by ~ ef2gh and ~ ef4ghb for ` eta ` away from the ordinates of the zeros of ` g ` ( ~ ef6gc , ~ ef6gd ), the abscissa by ~ ef3sig , the cuts by ~ ef4cut , then ~ ef6core ).')
    A0, G = ante_of(S['ef6cnt'])
    c = Ctx(w, A0)
    yr = c.g('Y e. RR'); y100 = c.g('; ; 1 0 0 <_ Y'); tr = c.g('T e. RR'); t2 = c.g('2 <_ T')
    dd = c.a1(w.s([], 'ef2dde', DD(ETA, '1')), DD(ETA, '1'))
    lv = {'T': tr, 'Y': yr}
    gcs = c([c([tr, t2], 'jca', '( T e. RR /\\ 2 <_ T )'), w.inst('ef6gc')], 'syl', ante_of(S['ef6gc'])[1])
    gfin = c([gcs, w.inst('simp1')], 'syl', '%s e. Fin' % GG); gss = c([gcs, w.inst('simp2')], 'syl', '%s C_ RR' % GG); gcard = c([gcs, w.inst('simp3')], 'syl', '( # ` %s ) <_ ( ; 1 6 x. %s )' % (GG, L4))
    spec0 = {DD(ETA, '1'): dd, '%s e. Fin' % GG: gfin, '%s C_ RR' % GG: gss, '( # ` %s ) <_ ( ; 1 6 x. %s )' % (GG, L4): gcard}
    GH = tsub(stmt('ef2gh'), {'F': ETA, 'A': '1', 'G': GG})
    gha, ghc = ante_of(GH)
    top = c([rebuild(w, c, gha, spec0), w.inst('ef2gh')], 'syl', ghc)
    GB_ = tsub(stmt('ef4ghb'), {'F': ETA, 'A': '1', 'G': GG})
    gba, gbc = ante_of(GB_)
    bot = c([rebuild(w, c, gba, spec0), w.inst('ef4ghb')], 'syl', gbc)
    IV = '( T [,] ( T + 1 ) )'
    def upgrade(st, fc, sel):
        body = fc.split(' e. %s ' % IV, 1)[1]
        GAPX, GE = top_and(body)
        Au = '( %s /\\ u e. %s )' % (A0, IV)
        Ab = '( %s /\\ %s )' % (Au, body)
        cb_ = Ctx(w, Ab)
        GDs = tsub(S['ef6gd'], {'H': 'u'})
        gda, gdc = ante_of(GDs)
        gdst = cb_([cb_([cb_([lift(w, tr, Ab), lift(w, t2, Ab)], 'jca', '( T e. RR /\\ 2 <_ T )'), cb_([w.s([w.s([], 'simpr', '( %s -> u e. %s )' % (Au, IV))], 'adantr', '( %s -> u e. %s )' % (Ab, IV)),
                                                                                                 cb_([cb_([], 'simpr', body), w.inst('simpl')], 'syl', GAPX)], 'jca', top_and(gda)[1])], 'jca', gda), w.inst('ef6gd')], 'syl', gdc)
        GG_ = top_and(gdc)[0 if sel == 0 else 1]
        gsel = cb_([gdst, w.inst('simpl' if sel == 0 else 'simpr')], 'syl', GG_)
        ge = cb_([cb_([], 'simpr', body), w.inst('simpr')], 'syl', GE)
        NB = '( %s /\\ %s )' % (GE, GG_)
        nb = cb_([ge, gsel], 'jca', NB)
        imp = w.s([nb], 'ex', '( %s -> ( %s -> %s ) )' % (Au, body, NB))
        return c([st, c([imp], 'reximdva', '( E. u e. %s %s -> E. u e. %s %s )' % (IV, body, IV, NB))], 'mpd', 'E. u e. %s %s' % (IV, NB)), NB
    top2, RT = upgrade(top, ghc, 0)
    bot2, RB0 = upgrade(bot, gbc, 1)
    cbr, RBy = cbvral_rex(w, IV, 'u', 'y', RB0)
    bot3 = c([bot2, c.a1(cbr, '( E. u e. %s %s <-> E. y e. %s %s )' % (IV, RB0, IV, RBy))], 'mpbid', 'E. y e. %s %s' % (IV, RBy))
    A1 = '( ( %s /\\ u e. %s ) /\\ %s )' % (A0, IV, RT)
    A2 = '( ( %s /\\ y e. %s ) /\\ %s )' % (A1, IV, RBy)
    c2 = Ctx(w, A2)
    L2 = lambda st: lift(w, st, A2)
    t1r = c2([L2(tr), numst(w, A2, '1', 'RR')], 'readdcld', '( T + 1 ) e. RR')
    uin = lift(w, w.s([w.s([], 'simpr', '( ( %s /\\ u e. %s ) -> u e. %s )' % (A0, IV, IV))], 'adantr', '( %s -> u e. %s )' % (A1, IV)), A2)
    yin = w.s([w.s([], 'simpr', '( ( %s /\\ y e. %s ) -> y e. %s )' % (A1, IV, IV))], 'adantr', '( %s -> y e. %s )' % (A2, IV))
    urr, tu_, u1_ = icc_out(c2, 'u', 'T', '( T + 1 )', uin, L2(tr), t1r)
    yrr, ty_, y1_ = icc_out(c2, 'y', 'T', '( T + 1 )', yin, L2(tr), t1r)
    rt2 = lift(w, w.s([], 'simpr', '( %s -> %s )' % (A1, RT)), A2)
    rb2 = c2([], 'simpr', RBy)
    goodu, gut = conj_split(w, A2, rt2)
    goody, gyb = conj_split(w, A2, rb2)
    GD2 = tsub(HGDX(ETA), {'U': 'y', 'V': 'u'})
    fm = lambda st: [l for l in w.lines if l.startswith(st + ':')][0].split(' |- ', 1)[1]
    GY, GU = ante_of(fm(goody))[1], ante_of(fm(goodu))[1]
    gd = c2([c2([goody, goodu], 'jca', '( %s /\\ %s )' % (GY, GU)), c2.a1(w.s([], 'r19.26', '( %s <-> ( %s /\\ %s ) )' % (GD2, GY, GU)), '( %s <-> ( %s /\\ %s ) )' % (GD2, GY, GU))], 'mpbird', GD2)
    GD2G = tsub(HGDX(GF), {'U': 'y', 'V': 'u'})
    GYG, GUG = ante_of(fm(gyb))[1], ante_of(fm(gut))[1]
    gdG = c2([c2([gyb, gut], 'jca', '( %s /\\ %s )' % (GYG, GUG)), c2.a1(w.s([], 'r19.26', '( %s <-> ( %s /\\ %s ) )' % (GD2G, GYG, GUG)), '( %s <-> ( %s /\\ %s ) )' % (GD2G, GYG, GUG))], 'mpbird', GD2G)
    # sigma
    MM = '( |^ ` ( 2 x. ( y + u ) ) )'
    tyu = c2([numst(w, A2, '2', 'RR'), c2([yrr, urr], 'readdcld', '( y + u ) e. RR')], 'remulcld', '( 2 x. ( y + u ) ) e. RR')
    mz = c2([tyu, w.inst('ceilcl')], 'syl', '%s e. ZZ' % MM)
    mr = c2([mz], 'zred', '%s e. RR' % MM)
    mge = c2([tyu, w.inst('ceilge')], 'syl', '( 2 x. ( y + u ) ) <_ %s' % MM)
    mlt = c2([tyu, w.inst('ceilm1lt')], 'syl', '( %s - 1 ) < ( 2 x. ( y + u ) )' % MM)
    lvm = {'y': yrr, 'u': urr, 'T': L2(tr), MM: mr}
    hy = [mge, mlt, ty_, y1_, tu_, u1_, L2(t2)]
    mn0 = c2([c2([mz, lin8(w, A2, hy, '0 <_ %s' % MM, lvm)], 'jca', '( %s e. ZZ /\\ 0 <_ %s )' % (MM, MM)), c2.a1(w.s([], 'elnn0z', '( %s e. NN0 <-> ( %s e. ZZ /\\ 0 <_ %s ) )' % (MM, MM, MM)), '( %s e. NN0 <-> ( %s e. ZZ /\\ 0 <_ %s ) )' % (MM, MM, MM))], 'mpbird', '%s e. NN0' % MM)
    PMM = '( -u y + ( %s / 2 ) )' % MM
    ddg = c2.a1(w.s([], 'ef2ddg', DD(GF, '1')), DD(GF, '1'))
    t4r = c2([L2(tr), numst(w, A2, '4', 'RR')], 'readdcld', '( T + 4 ) e. RR')
    def bzfin(F, ddst, BZX):
        BZI = tsub(stmt('ef3bz'), {'F': F, 'A': '1', 'U': '( T + 4 )'})
        bza, bzc = ante_of(BZI)
        bzs = c2([c2([ddst, t4r], 'jca', bza), w.inst('ef3bz')], 'syl', bzc)
        return c2([bzs, w.inst('simpl')], 'syl', '%s e. Fin' % BZX)
    bzfE = bzfin(ETA, L2(dd), BZE4); bzfG = bzfin(GF, ddg, BZG4)
    def imfin(fn, bzf, BZX):
        ff = w.s([], 'ref' if fn == 'Re' else 'imf', '%s : CC --> RR' % fn)
        fun = c2.a1(w.s([ff, w.inst('ffun')], 'ax-mp', 'Fun %s' % fn), 'Fun %s' % fn)
        return c2([fun, bzf, w.inst('imafi')], 'syl2anc', '( %s " %s ) e. Fin' % (fn, BZX)), ff
    reE, _ = imfin('Re', bzfE, BZE4); reG, _ = imfin('Re', bzfG, BZG4)
    imE, imff = imfin('Im', bzfE, BZE4); imG, _ = imfin('Im', bzfG, BZG4)
    REU = '( ( Re " %s ) u. ( Re " %s ) )' % (BZE4, BZG4)
    IMU = '( ( Im " %s ) u. ( Im " %s ) )' % (BZE4, BZG4)
    ref_ = c2([reE, reG, w.inst('unfi')], 'syl2anc', '%s e. Fin' % REU)
    imf_ = c2([imE, imG, w.inst('unfi')], 'syl2anc', '%s e. Fin' % IMU)
    SG = tsub(stmt('ef3sig'), {'F': ETA, 'A': '1', 'P': '-u y', 'M': MM, 'B': REU})
    sga, sgc = ante_of(SG)
    sspec = {DD(ETA, '1'): L2(dd), '-u y e. RR': c2([yrr], 'renegcld', '-u y e. RR'), '-u ( T + 1 ) <_ -u y': lin8(w, A2, hy, '-u ( T + 1 ) <_ -u y', lvm), '-u y <_ 0': lin8(w, A2, hy, '-u y <_ 0', lvm),
             '%s e. NN0' % MM: mn0, '0 <_ %s' % PMM: lin8(w, A2, hy, '0 <_ %s' % PMM, lvm), '%s <_ ( T + 2 )' % PMM: lin8(w, A2, hy, '%s <_ ( T + 2 )' % PMM, lvm), '%s e. Fin' % REU: ref_}
    sg = c2([rebuild(w, c2, sga, sspec), w.inst('ef3sig')], 'syl', sgc)
    SIGB = sgc.split(' e. ( ( 9 / ; 1 6 ) [,] ( 5 / 8 ) ) ', 1)[1]
    A3 = '( ( %s /\\ a e. ( ( 9 / ; 1 6 ) [,] ( 5 / 8 ) ) ) /\\ %s )' % (A2, SIGB)
    c3 = Ctx(w, A3)
    L3 = lambda st: lift(w, st, A3)
    ain = w.s([w.s([], 'simpr', '( ( %s /\\ a e. ( ( 9 / ; 1 6 ) [,] ( 5 / 8 ) ) ) -> a e. ( ( 9 / ; 1 6 ) [,] ( 5 / 8 ) ) )' % A2)], 'adantr', '( %s -> a e. ( ( 9 / ; 1 6 ) [,] ( 5 / 8 ) ) )' % A3)
    ar_, a916, a58 = icc_out(c3, 'a', '( 9 / ; 1 6 )', '( 5 / 8 )', ain, numst(w, A3, '( 9 / ; 1 6 )', 'RR'), numst(w, A3, '( 5 / 8 )', 'RR'))
    # cuts
    CU = tsub(stmt('ef4cut'), {'B': IMU, 'P': '-u y', 'Q': 'u'})
    cua, cuc = ante_of(CU)
    imsE = w.s([w.s([], 'imassrn', '( Im " %s ) C_ ran Im' % BZE4), w.s([imff, w.inst('frn')], 'ax-mp', 'ran Im C_ RR')], 'sstri', '( Im " %s ) C_ RR' % BZE4)
    imsG = w.s([w.s([], 'imassrn', '( Im " %s ) C_ ran Im' % BZG4), w.s([imff, w.inst('frn')], 'ax-mp', 'ran Im C_ RR')], 'sstri', '( Im " %s ) C_ RR' % BZG4)
    imss = c3.a1(w.s([imsE, imsG], 'unssi', '%s C_ RR' % IMU), '%s C_ RR' % IMU)
    cspec = {'%s e. Fin' % IMU: L3(imf_), '%s C_ RR' % IMU: imss, '-u y e. RR': c3([L3(yrr)], 'renegcld', '-u y e. RR'), 'u e. RR': L3(urr),
             '1 <_ ( u - -u y )': lin8(w, A3, [L3(h) for h in hy], '1 <_ ( u - -u y )', {k: L3(v) for k, v in lvm.items()})}
    cut = c3([rebuild(w, c3, cua, cspec), w.inst('ef4cut')], 'syl', cuc)
    BODY = cuc[len('E. m e. NN E. g '):]
    A4 = '( ( %s /\\ m e. NN ) /\\ %s )' % (A3, BODY)
    c4 = Ctx(w, A4)
    CO = tsub(S['ef6core'], {'U': 'y', 'V': 'u', 'S': 'a', 'M': MM, 'K': 'm', 'G': 'g'})
    coa, coc = ante_of(CO)
    L4_ = lambda st: lift(w, st, A4)
    # the sigma body gives -. a e. REU: split
    nre = c3([], 'x', 'x') if False else None
    sigb = c3([], 'simpr', SIGB)
    nreu = c3([sigb, w.inst('simpl')], 'syl', '-. a e. %s' % REU)
    def nsplit(ctx, st, X, Y, x):
        e1 = w.s([w.s([], 'elun1', '( %s e. %s -> %s e. ( %s u. %s ) )' % (x, X, x, X, Y))], 'con3i', '( -. %s e. ( %s u. %s ) -> -. %s e. %s )' % (x, X, Y, x, X))
        e2 = w.s([w.s([], 'elun2', '( %s e. %s -> %s e. ( %s u. %s ) )' % (x, Y, x, X, Y))], 'con3i', '( -. %s e. ( %s u. %s ) -> -. %s e. %s )' % (x, X, Y, x, Y))
        return e1, e2
    r1, r2 = nsplit(c3, nreu, '( Re " %s )' % BZE4, '( Re " %s )' % BZG4, 'a')
    naE = c3([nreu, r1], 'syl', '-. a e. ( Re " %s )' % BZE4); naG = c3([nreu, r2], 'syl', '-. a e. ( Re " %s )' % BZG4)
    AVU = 'A. j e. ( 1 ..^ m ) -. ( g ` j ) e. %s' % IMU
    avu = c4.g(AVU)
    i1, i2 = nsplit(c4, avu, '( Im " %s )' % BZE4, '( Im " %s )' % BZG4, '( g ` j )')
    avE = c4([avu, c4.a1(w.s([i1], 'ralimi', '( %s -> A. j e. ( 1 ..^ m ) -. ( g ` j ) e. ( Im " %s ) )' % (AVU, BZE4)), '( %s -> A. j e. ( 1 ..^ m ) -. ( g ` j ) e. ( Im " %s ) )' % (AVU, BZE4))], 'mpd', 'A. j e. ( 1 ..^ m ) -. ( g ` j ) e. ( Im " %s )' % BZE4)
    avG = c4([avu, c4.a1(w.s([i2], 'ralimi', '( %s -> A. j e. ( 1 ..^ m ) -. ( g ` j ) e. ( Im " %s ) )' % (AVU, BZG4)), '( %s -> A. j e. ( 1 ..^ m ) -. ( g ` j ) e. ( Im " %s ) )' % (AVU, BZG4))], 'mpd', 'A. j e. ( 1 ..^ m ) -. ( g ` j ) e. ( Im " %s )' % BZG4)
    kspec = {'y e. RR': L4_(yrr), 'u e. RR': L4_(urr), 'T <_ y': L4_(ty_), 'y <_ ( T + 1 )': L4_(y1_), 'T <_ u': L4_(tu_), 'u <_ ( T + 1 )': L4_(u1_), GD2: L4_(gd), GD2G: L4_(gdG),
             'a e. RR': L4_(ar_), '( 9 / ; 1 6 ) <_ a': L4_(a916), 'a <_ ( 5 / 8 )': L4_(a58), '%s e. NN0' % MM: L4_(mn0),
             '-. a e. ( Re " %s )' % BZE4: L4_(naE), '-. a e. ( Re " %s )' % BZG4: L4_(naG),
             'A. j e. ( 1 ..^ m ) -. ( g ` j ) e. ( Im " %s )' % BZE4: avE, 'A. j e. ( 1 ..^ m ) -. ( g ` j ) e. ( Im " %s )' % BZG4: avG,
             'u <_ ( -u y + ( %s / 2 ) )' % MM: L4_(lin8(w, A2, hy, 'u <_ ( -u y + ( %s / 2 ) )' % MM, lvm)), '( -u y + ( %s / 2 ) ) <_ ( T + 2 )' % MM: L4_(sspec['%s <_ ( T + 2 )' % PMM])}
    co = c4([rebuild(w, c4, coa, kspec), w.inst('ef6core')], 'syl', coc)
    e1 = w.s([co], 'ex', '( ( %s /\\ m e. NN ) -> ( %s -> %s ) )' % (A3, BODY, G))
    e2 = w.s([e1], 'exlimdv', '( ( %s /\\ m e. NN ) -> ( E. g %s -> %s ) )' % (A3, BODY, G))
    e3 = c3([e2], 'rexlimdva', '( %s -> %s )' % (cuc, G))
    e4 = c3([cut, e3], 'mpd', G)
    e5 = w.s([e4], 'ex', '( ( %s /\\ a e. ( ( 9 / ; 1 6 ) [,] ( 5 / 8 ) ) ) -> ( %s -> %s ) )' % (A2, SIGB, G))
    e6 = c2([e5], 'rexlimdva', '( %s -> %s )' % (sgc, G))
    e7 = c2([sg, e6], 'mpd', G)
    e8 = w.s([e7], 'ex', '( ( %s /\\ y e. %s ) -> ( %s -> %s ) )' % (A1, IV, RBy, G))
    c1 = Ctx(w, A1)
    e9 = c1([e8], 'rexlimdva', '( E. y e. %s %s -> %s )' % (IV, RBy, G))
    e10 = c1([lift(w, bot3, A1), e9], 'mpd', G)
    e11 = w.s([e10], 'ex', '( ( %s /\\ u e. %s ) -> ( %s -> %s ) )' % (A0, IV, RT, G))
    e12 = c([e11], 'rexlimdva', '( E. u e. %s %s -> %s )' % (IV, RT, G))
    w.qed([top2, e12], 'mpd', S['ef6cnt'])
    return run8(w)


def cbvral_rex(w, X, var, new, body):
    eq, nb = w.wcongr(body, {var: new}, '%s = %s' % (var, new), {var: w.s([], 'id', '( %s = %s -> %s = %s )' % (var, new, var, new))})
    return w.s([eq], 'cbvrexvw', '( E. %s e. %s %s <-> E. %s e. %s %s )' % (var, X, body, new, X, nb)), nb





GENS = {'ef6cnt': gen_cnt}
if __name__ == '__main__':
    for f in (sys.argv[1:] or list(GENS)):
        GENS[f]()
