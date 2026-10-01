"""Sortie ZC1: the identity theorem on the right half-plane from agreement on Re > 1 (hp0id)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zc1lib import *
from cl import lift
import congr as _cg
import num
from c8_o import numst
from c9_b import decode
from c10_f import crfacts, clo
import zc1_i
from zc1_i import encode
import lin
lin.FASTPATH = True


def hp_rect(w, A0, P, ph):
    """the rectangle [ a , Re P + 2 ] c [ - abs Im P , abs Im P ], a = Re P / ( Re P + 1 ), margin a / 2, inside HP0,
    containing P and 2; ph : ( A0 -> P e. HP0 )"""
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    el = s([s([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), w.inst('elhp2')], 'syl', '( %s e. %s <-> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (P, HP0, P, P))
    pp = s([ph, el], 'mpbid', '( %s e. CC /\\ 0 < ( Re ` %s ) )' % (P, P))
    pc = s([pp, w.inst('simpl')], 'syl', '%s e. CC' % P); rp0 = s([pp, w.inst('simpr')], 'syl', '0 < ( Re ` %s )' % P)
    RP, IP = '( Re ` %s )' % P, '( Im ` %s )' % P
    rpr = s([pc], 'recld', '%s e. RR' % RP); ipr = s([pc], 'imcld', '%s e. RR' % IP)
    AI = '( abs ` %s )' % IP
    air = s([s([ipr], 'recnd', '%s e. CC' % IP)], 'abscld', '%s e. RR' % AI)
    RP1 = '( %s + 1 )' % RP
    rp1 = s([rpr, s([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR')], 'readdcld', '%s e. RR' % RP1)
    rp1p = s([rp1, lin8(w, A0, [rp0], '0 < %s' % RP1, {RP: rpr})], 'elrpd', '%s e. RR+' % RP1)
    a_ = '( %s / %s )' % (RP, RP1)
    ar = s([rpr, rp1p], 'rerpdivcld', '%s e. RR' % a_)
    rpp = s([rpr, rp0], 'elrpd', '%s e. RR+' % RP)
    ap = s([rpp, rp1p], 'rpdivcld', '%s e. RR+' % a_)
    lvp = {RP: rpr}
    hint = s([rpr, rpr, lin8(w, A0, [rp0], '0 <_ %s' % RP, lvp), lin8(w, A0, [rp0], '0 <_ %s' % RP, lvp)], 'mulge0d', '0 <_ ( %s x. %s )' % (RP, RP))
    import cl as _cl
    c = _cl.Closure(w, A0, lvp); c.atom(RP)
    le1 = s([lin.linarith(w, A0, [hint], '%s <_ ( %s x. %s )' % (RP, RP1, RP), closure=c, products=True),
             s([rpr, rpr, rp1p], 'ledivmuld', '( %s <_ %s <-> %s <_ ( %s x. %s ) )' % (a_, RP, RP, RP1, RP))], 'mpbird', '%s <_ %s' % (a_, RP))
    le2 = s([lin8(w, A0, [], '%s <_ ( %s x. 1 )' % (RP, RP1), lvp), s([rpr, s([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR'), rp1p], 'ledivmuld',
             '( %s <_ 1 <-> %s <_ ( %s x. 1 ) )' % (a_, RP, RP1))], 'mpbird', '%s <_ 1' % a_)
    R_ = '( %s / 2 )' % a_
    rr = s([ap, w.inst('rphalfcld')], 'syl', '%s e. RR+' % R_)
    A = '( %s + ( _i x. -u %s ) )' % (a_, AI)
    B = '( ( %s + 2 ) + ( _i x. %s ) )' % (RP, AI)
    nai = s([air], 'renegcld', '-u %s e. RR' % AI)
    rp2 = s([rpr, numst(w, A0, '2', 'RR')], 'readdcld', '( %s + 2 ) e. RR' % RP)
    ac, reA, imA = crfacts(w, A0, a_, '-u %s' % AI, ar, nai)
    bc, reB, imB = crfacts(w, A0, '( %s + 2 )' % RP, AI, rp2, air)
    lv = {RP: rpr, IP: ipr, AI: air, a_: ar}
    for e, st in (('( Re ` %s )' % A, ac), ('( Im ` %s )' % A, ac), ('( Re ` %s )' % B, bc), ('( Im ` %s )' % B, bc)):
        lv[e] = s([st], 'recld' if e.startswith('( Re') else 'imcld', '%s e. RR' % e)
    ag0 = s([s([ipr], 'recnd', '%s e. CC' % IP)], 'absge0d', '0 <_ %s' % AI)
    lt = s([ipr], 'leabsd', '%s <_ %s' % (IP, AI))
    nt = s([s([s([ipr], 'renegcld', '-u %s e. RR' % IP)], 'leabsd', '-u %s <_ ( abs ` -u %s )' % (IP, IP)), s([s([ipr], 'recnd', '%s e. CC' % IP)], 'absnegd', '( abs ` -u %s ) = %s' % (IP, AI))],
            'breqtrd', '-u %s <_ %s' % (IP, AI))
    hy = [reA, imA, reB, imB, le1, le2, ag0, lt, nt, rp0]
    geo = s([lin8(w, A0, hy, '( Re ` %s ) <_ ( Re ` %s )' % (A, B), lv), lin8(w, A0, hy, '( Im ` %s ) <_ ( Im ` %s )' % (A, B), lv)], 'jca', GEOG(A, B))
    # the fattened rectangle lies in HP0
    RR_ = '( %s + ( _i x. %s ) )' % (R_, R_)
    A2, B2 = '( %s - %s )' % (A, RR_), '( %s + %s )' % (B, RR_)
    rrc = s([s([rr], 'rpcnd', '%s e. CC' % R_), s([s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '_i e. CC'), s([rr], 'rpcnd', '%s e. CC' % R_)], 'mulcld', '( _i x. %s ) e. CC' % R_)], 'addcld', '%s e. CC' % RR_)
    a2c = s([ac, rrc], 'subcld', '%s e. CC' % A2); b2c = s([bc, rrc], 'addcld', '%s e. CC' % B2)
    ra2 = s([ac, rrc], 'resubd', '( Re ` %s ) = ( ( Re ` %s ) - ( Re ` %s ) )' % (A2, A, RR_))
    rrr = s([s([rr], 'rpred', '%s e. RR' % R_), s([rr], 'rpred', '%s e. RR' % R_)], 'crred', '( Re ` %s ) = %s' % (RR_, R_))
    RECT = '( %s crect %s )' % (A2, B2)
    Ax = '( %s /\\ c e. %s )' % (A0, RECT)
    L = lambda st: lift(w, st, Ax)
    dx = decode(w, Ax, w.s([], 'simpr', '( %s -> c e. %s )' % (Ax, RECT)), L(a2c), L(b2c), A2, B2, RECT, U='c')
    xc = dx[0]
    lvx = {'( Re ` c )': w.s([xc], 'recld', '( %s -> ( Re ` c ) e. RR )' % Ax), '( Re ` %s )' % A2: w.s([L(a2c)], 'recld', '( %s -> ( Re ` %s ) e. RR )' % (Ax, A2)),
           '( Re ` %s )' % A: L(lv['( Re ` %s )' % A]), '( Re ` %s )' % RR_: w.s([L(rrc)], 'recld', '( %s -> ( Re ` %s ) e. RR )' % (Ax, RR_)), a_: L(ar)}
    ahalf = lin8(w, A0, [], '0 < %s' % a_, {a_: ar}) if False else s([ap], 'rpgt0d', '0 < %s' % a_)
    rx = lin8(w, Ax, [dx[1], L(ra2), L(rrr), L(reA), L(ahalf)], '0 < ( Re ` c )', lvx)
    elx = w.s([w.s([w.s([], '0re', '0 e. RR')], 'a1i', '( %s -> 0 e. RR )' % Ax), w.inst('elhp2')], 'syl', '( %s -> ( c e. %s <-> ( c e. CC /\\ 0 < ( Re ` c ) ) ) )' % (Ax, HP0))
    xh = w.s([w.s([xc, rx], 'jca', '( %s -> ( c e. CC /\\ 0 < ( Re ` c ) ) )' % Ax), elx], 'mpbird', '( %s -> c e. %s )' % (Ax, HP0))
    sub = s([w.s([xh], 'ex', '( %s -> ( c e. %s -> c e. %s ) )' % (A0, RECT, HP0))], 'ssrdv', '%s C_ %s' % (RECT, HP0))
    # P and 2 in the rectangle
    pin = encode(w, A0, pc, ac, bc, A, B, P, lin8(w, A0, hy, '( Re ` %s ) <_ %s' % (A, RP), lv), lin8(w, A0, hy, '%s <_ ( Re ` %s )' % (RP, B), lv),
                 lin8(w, A0, hy, '( Im ` %s ) <_ %s' % (A, IP), lv), lin8(w, A0, hy, '%s <_ ( Im ` %s )' % (IP, B), lv))
    two = s([], '2cnd', '2 e. CC')
    re2 = s([w.s([], 're2' if False else 'rei', '( Re ` 2 ) = 2')], 'a1i', '( Re ` 2 ) = 2') if False else s([s([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR')], 'rered', '( Re ` 2 ) = 2')
    im2 = s([s([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR')], 'reim0d', '( Im ` 2 ) = 0')
    lv2 = dict(lv); lv2['( Re ` 2 )'] = s([two], 'recld', '( Re ` 2 ) e. RR'); lv2['( Im ` 2 )'] = s([two], 'imcld', '( Im ` 2 ) e. RR')
    hy2 = hy + [re2, im2]
    tin = encode(w, A0, two, ac, bc, A, B, '2', lin8(w, A0, hy2, '( Re ` %s ) <_ ( Re ` 2 )' % A, lv2), lin8(w, A0, hy2, '( Re ` 2 ) <_ ( Re ` %s )' % B, lv2),
                 lin8(w, A0, hy2, '( Im ` %s ) <_ ( Im ` 2 )' % A, lv2), lin8(w, A0, hy2, '( Im ` 2 ) <_ ( Im ` %s )' % B, lv2))
    return dict(A=A, B=B, R=R_, ac=ac, bc=bc, geo=geo, rr=rr, sub=sub, pin=pin, tin=tin, pc=pc)


HPF = HOLF('F', HP0)
HPG = HOLF('G', HP0)
S['hp0id'] = '( ( %s /\\ %s /\\ A. v e. %s ( 1 < ( Re ` v ) -> ( F ` v ) = ( G ` v ) ) ) -> A. z e. %s ( F ` z ) = ( G ` z ) )' % (HPF, HPG, HP0, HP0)


def gen_hp0id():
    w = W('hp0id', 'Identity theorem on the right half-plane: two holomorphic functions there that agree on ` 1 < Re z ` agree everywhere ( ~ holidrect on the rectangle ` [ a , Re z + 2 ] x. [ - abs Im z , abs Im z ] ` , the difference vanishing on the unit disc about ` 2 ` ).')
    A0, GC = ante_of(S['hp0id'])
    X1, X2, X3 = top_and(A0)
    Az = '( %s /\\ z e. %s )' % (A0, HP0)
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Az, f))
    L = lambda st: lift(w, st, Az)
    fh = s([], 'simpl1', X1); gh = s([], 'simpl2', X2); agr = s([], 'simpl3', X3)
    zh = s([], 'simpr', 'z e. %s' % HP0)
    R = hp_rect(w, Az, 'z', zh)
    HM = '( u e. %s |-> ( ( F ` u ) - ( G ` u ) ) )' % HP0
    hh = s([s([fh, gh], 'jca', '( %s /\\ %s )' % (X1, X2)), w.inst('zl2hsub')], 'syl', HOLF(HM, HP0))
    def hval(ante, U, ust):
        VAL = '( ( F ` %s ) - ( G ` %s ) )' % (U, U)
        vx = w.s([w.s([], 'ovex', '%s e. _V' % VAL)], 'a1i', '( %s -> %s e. _V )' % (ante, VAL))
        fv, _ = _cg.mptval(w, ante, 'u', HP0, '( ( F ` u ) - ( G ` u ) )', U, ust, exs=vx, gen=w.g)
        return fv, VAL
    # the ball of radius 1 about 2
    Aw = '( ( %s /\\ w e. %s ) /\\ ( abs ` ( w - 2 ) ) < 1 )' % (Az, HP0)
    sw = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Aw, f))
    wh = sw([], 'simplr', 'w e. %s' % HP0)
    wc = sw([sw([wh, sw([sw([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), w.inst('elhp2')], 'syl', '( w e. %s <-> ( w e. CC /\\ 0 < ( Re ` w ) ) )' % HP0)], 'mpbid',
                 '( w e. CC /\\ 0 < ( Re ` w ) )'), w.inst('simpl')], 'syl', 'w e. CC')
    wd = sw([wc, sw([], '2cnd', '2 e. CC')], 'subcld', '( w - 2 ) e. CC')
    ar = sw([wd, w.inst('absrele')], 'syl', '( abs ` ( Re ` ( w - 2 ) ) ) <_ ( abs ` ( w - 2 ) )')
    rw2 = sw([wc, sw([], '2cnd', '2 e. CC')], 'resubd', '( Re ` ( w - 2 ) ) = ( ( Re ` w ) - ( Re ` 2 ) )')
    re2 = sw([sw([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR')], 'rered', '( Re ` 2 ) = 2')
    RW = '( Re ` ( w - 2 ) )'
    rwr = sw([wd], 'recld', '%s e. RR' % RW)
    lt1 = sw([], 'simpr', '( abs ` ( w - 2 ) ) < 1')
    ab1 = sw([sw([sw([rwr], 'recnd', '%s e. CC' % RW)], 'abscld', '( abs ` %s ) e. RR' % RW), sw([wd], 'abscld', '( abs ` ( w - 2 ) ) e. RR'), sw([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR'), ar, lt1],
             'lelttrd', '( abs ` %s ) < 1' % RW)
    al = sw([ab1, sw([rwr, sw([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR')], 'abslt', '( ( abs ` %s ) < 1 <-> ( -u 1 < %s /\\ %s < 1 ) )' % (RW, RW, RW))], 'mpbid', '( -u 1 < %s /\\ %s < 1 )' % (RW, RW)) if False else \
        sw([ab1, sw([sw([rwr, sw([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR')], 'jca', '( %s e. RR /\\ 1 e. RR )' % RW), w.inst('abslt')], 'syl', '( ( abs ` %s ) < 1 <-> ( -u 1 < %s /\\ %s < 1 ) )' % (RW, RW, RW))],
           'mpbid', '( -u 1 < %s /\\ %s < 1 )' % (RW, RW))
    rwg = sw([al, w.inst('simpl')], 'syl', '-u 1 < %s' % RW)
    g1 = lin8(w, Aw, [rwg, rw2, re2], '1 < ( Re ` w )', {RW: rwr, '( Re ` w )': sw([wc], 'recld', '( Re ` w ) e. RR'), '( Re ` 2 )': sw([sw([], '2cnd', '2 e. CC')], 'recld', '( Re ` 2 ) e. RR')})
    BV = '( 1 < ( Re ` v ) -> ( F ` v ) = ( G ` v ) )'
    BW = '( 1 < ( Re ` w ) -> ( F ` w ) = ( G ` w ) )'
    eqv = w.wcongr(BV, {'v': 'w'}, 'v = w', {'v': w.s([], 'id', '( v = w -> v = w )')})[0]
    bw = sw([eqv, lift(w, agr, Aw), wh], 'rspcdva', BW)
    fgw = sw([g1, bw], 'mpd', '( F ` w ) = ( G ` w )')
    fvw, VW = hval(Aw, 'w', wh)
    fwc = sw([sw([sw([lift(w, fh, Aw), w.inst('simpl')], 'syl', 'F e. ( %s -cn-> CC )' % HP0), w.inst('cncff')], 'syl', 'F : %s --> CC' % HP0), wh], 'ffvelcdmd', '( F ` w ) e. CC')
    gwc = sw([sw([sw([lift(w, gh, Aw), w.inst('simpl')], 'syl', 'G e. ( %s -cn-> CC )' % HP0), w.inst('cncff')], 'syl', 'G : %s --> CC' % HP0), wh], 'ffvelcdmd', '( G ` w ) e. CC')
    hw0 = sw([fvw, sw([fwc, fgw], 'subeq0bd', '( ( F ` w ) - ( G ` w ) ) = 0')], 'eqtrd', '( %s ` w ) = 0' % HM)
    Aw0 = '( %s /\\ w e. %s )' % (Az, HP0)
    imp = w.s([hw0], 'ex', '( %s -> ( ( abs ` ( w - 2 ) ) < 1 -> ( %s ` w ) = 0 ) )' % (Aw0, HM))
    alw = s([imp], 'ralrimiva', 'A. w e. %s ( ( abs ` ( w - 2 ) ) < 1 -> ( %s ` w ) = 0 )' % (HP0, HM))
    ES = 'E. s e. RR+ A. w e. %s ( ( abs ` ( w - 2 ) ) < s -> ( %s ` w ) = 0 )' % (HP0, HM)
    esb = w.s([w.s([w.s([], 'breq2', '( s = 1 -> ( ( abs ` ( w - 2 ) ) < s <-> ( abs ` ( w - 2 ) ) < 1 ) )')], 'imbi1d',
                   '( s = 1 -> ( ( ( abs ` ( w - 2 ) ) < s -> ( %s ` w ) = 0 ) <-> ( ( abs ` ( w - 2 ) ) < 1 -> ( %s ` w ) = 0 ) ) )' % (HM, HM))], 'ralbidv',
              '( s = 1 -> ( A. w e. %s ( ( abs ` ( w - 2 ) ) < s -> ( %s ` w ) = 0 ) <-> A. w e. %s ( ( abs ` ( w - 2 ) ) < 1 -> ( %s ` w ) = 0 ) ) )' % (HP0, HM, HP0, HM))
    es = s([s([w.s([], '1rp', '1 e. RR+')], 'a1i', '1 e. RR+'), alw, w.s([esb], 'rspcev', '( ( 1 e. RR+ /\\ A. w e. %s ( ( abs ` ( w - 2 ) ) < 1 -> ( %s ` w ) = 0 ) ) -> %s )' % (HP0, HM, ES))], 'syl2anc', ES)
    HI = tsub(stmt('holidrect'), {'F': HM, 'D': HP0, 'A': R['A'], 'B': R['B'], 'R': R['R'], 'X': '2'})
    hia, hic = ante_of(HI)
    P0, PX = top_and(hia)
    Q1, Q2, Q3 = top_and(P0)
    hi = s([s([s([hh, s([s([R['ac'], R['bc']], 'jca', '( %s e. CC /\\ %s e. CC )' % (R['A'], R['B'])), R['geo']], 'jca', Q2), s([R['rr'], R['sub']], 'jca', Q3)], '3jca', P0),
               s([R['tin'], es], 'jca', PX)], 'jca', hia), w.inst('holidrect')], 'syl', hic)
    BY = '( %s ` y ) = 0' % HM
    eqy = w.s([w.s([], 'fveq2', '( y = z -> ( %s ` y ) = ( %s ` z ) )' % (HM, HM))], 'eqeq1d', '( y = z -> ( ( %s ` y ) = 0 <-> ( %s ` z ) = 0 ) )' % (HM, HM))
    hz0 = s([eqy, hi, R['pin']], 'rspcdva', '( %s ` z ) = 0' % HM)
    fvz, VZ = hval(Az, 'z', zh)
    fzc = s([s([s([fh, w.inst('simpl')], 'syl', 'F e. ( %s -cn-> CC )' % HP0), w.inst('cncff')], 'syl', 'F : %s --> CC' % HP0), zh], 'ffvelcdmd', '( F ` z ) e. CC') if False else \
        s([s([s([fh, w.inst('simpl')], 'syl', 'F e. ( %s -cn-> CC )' % HP0), w.inst('cncff')], 'syl', 'F : %s --> CC' % HP0), zh], 'ffvelcdmd', '( F ` z ) e. CC')
    gzc = s([s([s([gh, w.inst('simpl')], 'syl', 'G e. ( %s -cn-> CC )' % HP0), w.inst('cncff')], 'syl', 'G : %s --> CC' % HP0), zh], 'ffvelcdmd', '( G ` z ) e. CC')
    d0 = s([s([fvz], 'eqcomd', '%s = ( %s ` z )' % (VZ, HM)), hz0], 'eqtrd', '%s = 0' % VZ)
    fz = s([fzc, gzc, d0], 'subeq0bd' if False else 'subeq0bd', '( F ` z ) = ( G ` z )') if False else s([d0, s([fzc, gzc], 'subeq0ad', '( ( ( F ` z ) - ( G ` z ) ) = 0 <-> ( F ` z ) = ( G ` z ) )')], 'mpbid', '( F ` z ) = ( G ` z )')
    w.qed([w.s([fz], 'ralrimiva', '( %s -> A. z e. %s ( F ` z ) = ( G ` z ) )' % (A0, HP0))], 'idi', S['hp0id'])
    return run8(w)


if __name__ == '__main__':
    gen_hp0id()
