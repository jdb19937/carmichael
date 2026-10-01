"""Sortie EF2: balls and squares (ef2blm, ef2bsq, ef2sqo)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from ef2lib import *
from c8_o import numst
from c8_n import sqparts, sqre_at, sqcc
import lin
lin.FASTPATH = True

S['ef2blm'] = '( ( ( P e. CC /\\ E e. RR+ ) /\\ W e. %s ) -> ( W e. CC /\\ ( abs ` ( W - P ) ) < ( E / 4 ) ) )' % BL()
S['ef2bsq'] = '( ( P e. CC /\\ E e. RR+ ) -> %s C_ %s )' % (BL(), SQ('P', 'E'))
S['ef2sqo'] = '( ( D e. ( TopOpen ` CCfld ) /\\ P e. D /\\ P e. CC ) -> E. e e. RR+ %s C_ D )' % SQ('P', 'e')


def gen_blm():
    w = W('ef2blm', 'Membership in the open disc of radius ` E / 4 ` about ` P ` .')
    A0, GC = ante_of(S['ef2blm'])
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    pc = s([], 'simpll', 'P e. CC'); erp = s([], 'simplr', 'E e. RR+'); wb = s([], 'simpr', 'W e. %s' % BL())
    e4 = s([s([erp, numst(w, A0, '4', 'RR+')], 'rpdivcld', '( E / 4 ) e. RR+')], 'rpxrd', '( E / 4 ) e. RR*')
    met = s([w.s([], 'cnxmet', '( abs o. - ) e. ( *Met ` CC )')], 'a1i', '( abs o. - ) e. ( *Met ` CC )')
    eb = s([met, pc, e4, w.inst('elbl')], 'syl3anc', '( W e. %s <-> ( W e. CC /\\ ( P ( abs o. - ) W ) < ( E / 4 ) ) )' % BL())
    two = s([wb, eb], 'mpbid', '( W e. CC /\\ ( P ( abs o. - ) W ) < ( E / 4 ) )')
    wc = s([two, w.inst('simpl')], 'syl', 'W e. CC')
    lt = s([two, w.inst('simpr')], 'syl', '( P ( abs o. - ) W ) < ( E / 4 )')
    md = s([pc, wc, w.s([w.s([], 'eqid', '( abs o. - ) = ( abs o. - )')], 'cnmetdval', '( ( P e. CC /\\ W e. CC ) -> ( P ( abs o. - ) W ) = ( abs ` ( P - W ) ) )')],
           'syl2anc', '( P ( abs o. - ) W ) = ( abs ` ( P - W ) )')
    ms = s([md, s([pc, wc], 'abssubd', '( abs ` ( P - W ) ) = ( abs ` ( W - P ) )')], 'eqtrd', '( P ( abs o. - ) W ) = ( abs ` ( W - P ) )')
    w.qed([wc, s([ms, lt], 'eqbrtrrd', '( abs ` ( W - P ) ) < ( E / 4 )')], 'jca', S['ef2blm'])
    return run8(w)


def gen_bsq():
    w = W('ef2bsq', 'The open disc of radius ` E / 4 ` about ` P ` lies in the closed square of half-side ` E ` about ` P ` .')
    A0, GC = ante_of(S['ef2bsq'])
    Au = '( %s /\\ u e. %s )' % (A0, BL())
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Au, f))
    pc = s([], 'simpll', 'P e. CC'); erp = s([], 'simplr', 'E e. RR+')
    bm = s([s([s([pc, erp], 'jca', '( P e. CC /\\ E e. RR+ )'), s([], 'simpr', 'u e. %s' % BL())], 'jca', '( ( P e. CC /\\ E e. RR+ ) /\\ u e. %s )' % BL()),
            w.inst('ef2blm')], 'syl', '( u e. CC /\\ ( abs ` ( u - P ) ) < ( E / 4 ) )')
    uc = s([bm, w.inst('simpl')], 'syl', 'u e. CC'); lt = s([bm, w.inst('simpr')], 'syl', '( abs ` ( u - P ) ) < ( E / 4 )')
    er = s([erp], 'rpred', 'E e. RR')
    d = s([uc, pc], 'subcld', '( u - P ) e. CC')
    ad = s([d], 'abscld', '( abs ` ( u - P ) ) e. RR')
    e4 = s([er, numst(w, Au, '4', 'RR'), s([w.s([], '4ne0', '4 =/= 0')], 'a1i', '4 =/= 0')], 'redivcld', '( E / 4 ) e. RR')
    hy = []
    lv = {'E': er, '( abs ` ( u - P ) )': ad}
    for p, lem, sl in (('Re', 'absrele', 'resubd'), ('Im', 'absimle', 'imsubd')):
        pr = s([d], 'recld' if p == 'Re' else 'imcld', '( %s ` ( u - P ) ) e. RR' % p)
        ab = s([d, w.inst(lem)], 'syl', '( abs ` ( %s ` ( u - P ) ) ) <_ ( abs ` ( u - P ) )' % p)
        abr = s([s([pr], 'recnd', '( %s ` ( u - P ) ) e. CC' % p)], 'abscld', '( abs ` ( %s ` ( u - P ) ) ) e. RR' % p)
        le = lin8(w, Au, [ab, lt], '( abs ` ( %s ` ( u - P ) ) ) <_ ( E / 4 )' % p, {'( abs ` ( %s ` ( u - P ) ) )' % p: abr, '( abs ` ( u - P ) )': ad, 'E': er})
        bb = s([le, s([pr, e4], 'absled', '( ( abs ` ( %s ` ( u - P ) ) ) <_ ( E / 4 ) <-> ( -u ( E / 4 ) <_ ( %s ` ( u - P ) ) /\\ ( %s ` ( u - P ) ) <_ ( E / 4 ) ) )' % (p, p, p))], 'mpbid',
               '( -u ( E / 4 ) <_ ( %s ` ( u - P ) ) /\\ ( %s ` ( u - P ) ) <_ ( E / 4 ) )' % (p, p))
        hy += [s([bb, w.inst('simpl')], 'syl', '-u ( E / 4 ) <_ ( %s ` ( u - P ) )' % p), s([bb, w.inst('simpr')], 'syl', '( %s ` ( u - P ) ) <_ ( E / 4 )' % p),
               s([uc, pc], sl, '( %s ` ( u - P ) ) = ( ( %s ` u ) - ( %s ` P ) )' % (p, p, p))]
        lv['( %s ` ( u - P ) )' % p] = pr
    ps = sqparts(w, Au, sqre_at(w, Au, pc, er, c='P', r='E'), c='P', r='E')
    a, b = sqcc(w, Au, pc, er, c='P', r='E')
    for x, st in (('P', pc),):
        lv['( Re ` P )'] = s([pc], 'recld', '( Re ` P ) e. RR'); lv['( Im ` P )'] = s([pc], 'imcld', '( Im ` P ) e. RR')
    hy += ps + [s([erp], 'rpgt0d', '0 < E')]
    m = crect_in(w, Au, SQA('P', 'E'), SQB('P', 'E'), a, b, 'u', uc, hy, lv)
    w.qed([w.s([m], 'ex', '( %s -> ( u e. %s -> u e. %s ) )' % (A0, BL(), SQ('P', 'E')))], 'ssrdv', S['ef2bsq'])
    return run8(w)


def gen_sqo():
    w = W('ef2sqo', 'An open set of complex numbers contains a closed square about each of its points.')
    A0, GC = ante_of(S['ef2sqo'])
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    K = '( TopOpen ` CCfld )'
    do = s([], 'simp1', 'D e. %s' % K); pd = s([], 'simp2', 'P e. D'); pc = s([], 'simp3', 'P e. CC')
    met = s([w.s([], 'cnxmet', '( abs o. - ) e. ( *Met ` CC )')], 'a1i', '( abs o. - ) e. ( *Met ` CC )')
    kn = w.s([w.s([], 'eqid', '%s = %s' % (K, K))], 'cnfldtopn', '%s = ( MetOpen ` ( abs o. - ) )' % K)
    ex = s([met, do, pd, w.s([kn], 'mopni2', '( ( ( abs o. - ) e. ( *Met ` CC ) /\\ D e. %s /\\ P e. D ) -> E. x e. RR+ %s C_ D )' % (K, BL('P', 'x')))], 'syl3anc',
           'E. x e. RR+ %s C_ D' % BL('P', 'x'))
    Ax = '( ( %s /\\ x e. RR+ ) /\\ %s C_ D )' % (A0, BL('P', 'x'))
    sx = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Ax, f))
    xr = sx([], 'simplr', 'x e. RR+')
    x4 = sx([xr, numst(w, Ax, '4', 'RR+')], 'rpdivcld', '( x / 4 ) e. RR+')
    SQ4 = SQ('P', '( x / 4 )')
    Au = '( %s /\\ u e. %s )' % (Ax, SQ4)
    su = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Au, f))
    pcu = up(w, pc, Au); xru = up(w, xr, Au)
    uin = su([], 'simpr', 'u e. %s' % SQ4)
    x4r = su([up(w, x4, Au)], 'rpred', '( x / 4 ) e. RR')
    sm = su([su([pcu, x4r], 'jca', '( P e. CC /\\ ( x / 4 ) e. RR )'), uin, w.inst('sqmem')], 'syl2anc', '( abs ` ( u - P ) ) <_ ( 2 x. ( x / 4 ) )')
    a, b = sqcc(w, Au, pcu, x4r, c='P', r='( x / 4 )')
    uc = su([su([a, b, w.inst('crectss')], 'syl2anc', '%s C_ CC' % SQ4), uin], 'sseldd', 'u e. CC')
    xrr = su([xru], 'rpred', 'x e. RR')
    ad = su([su([uc, pcu], 'subcld', '( u - P ) e. CC')], 'abscld', '( abs ` ( u - P ) ) e. RR')
    lt = lin8(w, Au, [sm, su([xru], 'rpgt0d', '0 < x')], '( abs ` ( u - P ) ) < x', {'x': xrr, '( abs ` ( u - P ) )': ad})
    md = su([pcu, uc, w.s([w.s([], 'eqid', '( abs o. - ) = ( abs o. - )')], 'cnmetdval', '( ( P e. CC /\\ u e. CC ) -> ( P ( abs o. - ) u ) = ( abs ` ( P - u ) ) )')],
            'syl2anc', '( P ( abs o. - ) u ) = ( abs ` ( P - u ) )')
    ms = su([md, su([pcu, uc], 'abssubd', '( abs ` ( P - u ) ) = ( abs ` ( u - P ) )')], 'eqtrd', '( P ( abs o. - ) u ) = ( abs ` ( u - P ) )')
    eb = su([up(w, met, Au), pcu, su([xru], 'rpxrd', 'x e. RR*'), w.inst('elbl')], 'syl3anc', '( u e. %s <-> ( u e. CC /\\ ( P ( abs o. - ) u ) < x ) )' % BL('P', 'x'))
    ub = su([su([uc, su([ms, lt], 'eqbrtrd', '( P ( abs o. - ) u ) < x')], 'jca', '( u e. CC /\\ ( P ( abs o. - ) u ) < x )'), eb], 'mpbird', 'u e. %s' % BL('P', 'x'))
    sb = sx([w.s([ub], 'ex', '( %s -> ( u e. %s -> u e. %s ) )' % (Ax, SQ4, BL('P', 'x')))], 'ssrdv', '%s C_ %s' % (SQ4, BL('P', 'x')))
    sd = sx([sb, sx([], 'simpr', '%s C_ D' % BL('P', 'x'))], 'sstrd', '%s C_ D' % SQ4)
    ide = w.s([], 'id', '( e = ( x / 4 ) -> e = ( x / 4 ) )')
    cs, _ = w.wcongr('%s C_ D' % SQ('P', 'e'), {'e': '( x / 4 )'}, 'e = ( x / 4 )', {'e': ide})
    wit = sx([x4, sd, w.s([cs], 'rspcev', '( ( ( x / 4 ) e. RR+ /\\ %s C_ D ) -> %s )' % (SQ4, GC))], 'syl2anc', GC)
    w.qed([ex, w.s([w.s([wit], 'ex', '( ( %s /\\ x e. RR+ ) -> ( %s C_ D -> %s ) )' % (A0, BL('P', 'x'), GC))], 'rexlimdva', '( %s -> ( E. x e. RR+ %s C_ D -> %s ) )' % (A0, BL('P', 'x'), GC))],
          'mpd', S['ef2sqo'])
    return run8(w)


if __name__ == '__main__':
    for g in sys.argv[1:] or ['ef2blm', 'ef2bsq', 'ef2sqo']:
        {'ef2blm': gen_blm, 'ef2bsq': gen_bsq, 'ef2sqo': gen_sqo}[g]()
