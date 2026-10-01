"""Sortie C6b, part 3: the outer rectangle (holnest, holnhrm, holnid1,
holnid2, holnfac)."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')); from c6blib import *
import lin
from lin import linarith
lin.FASTPATH = True

INTX = INTG(AR, BR, 'X')
RBDX = RBDG(AR, BR, 'X')
HAX = '( %s /\\ X e. ( A crect B ) )' % HAN
HRMX = HRMG(AR, BR, 'X', 'R', 'm')
RAR = RE(AR); RBR = RE(BR); IAR = IM(AR); IBR = IM(BR); RX = RE('X'); IX = IM('X')

if __name__ == '__main__':
    # ---- holnest --------------------------------------------------------------------
    w = W('holnest', 'A point of a rectangle is interior to the rectangle enlarged by R in every direction, at distance at least R from its frame.')
    A0 = '( ( %s /\\ R e. RR+ ) /\\ X e. ( A crect B ) )' % AB
    ab = w.s([], 'simpll', '( %s -> %s )' % (A0, AB))
    Rrp = w.s([], 'simplr', '( %s -> R e. RR+ )' % A0)
    xin = w.s([], 'simpr', '( %s -> X e. ( A crect B ) )' % A0)
    e = rectel(w, A0, xin, ab)
    d = {'rr': w.s([Rrp], 'rpred', '( %s -> R e. RR )' % A0), 'ac': e['ac'], 'bc': e['bc']}
    d['rc'] = rc = w.s([d['rr']], 'recnd', '( %s -> R e. CC )' % A0)
    ic = closed(w, A0, 'ax-icn', '_i e. CC')
    d['sc'] = w.s([rc, w.s([ic, rc], 'mulcld', '( %s -> ( _i x. R ) e. CC )' % A0)], 'addcld', '( %s -> ( R + ( _i x. R ) ) e. CC )' % A0)
    r = reim(w, A0, d)
    rpos = w.s([Rrp], 'rpgt0d', '( %s -> 0 < R )' % A0)
    arc = w.s([e['ac'], d['sc']], 'subcld', '( %s -> %s e. CC )' % (A0, AR))
    brc = w.s([e['bc'], d['sc']], 'addcld', '( %s -> %s e. CC )' % (A0, BR))
    leaves = {RA: e['ar'], RB: e['br'], IA: e['ai'], IB: e['bi'], RX: e['xr'], IX: e['xi'], 'R': d['rr'],
              RAR: w.s([arc], 'recld', '( %s -> %s e. RR )' % (A0, RAR)), IAR: w.s([arc], 'imcld', '( %s -> %s e. RR )' % (A0, IAR)),
              RBR: w.s([brc], 'recld', '( %s -> %s e. RR )' % (A0, RBR)), IBR: w.s([brc], 'imcld', '( %s -> %s e. RR )' % (A0, IBR))}
    for k in list(leaves):
        leaves[k] = ('RR', leaves[k])
    l1 = linarith(w, A0, [r['rar'], e['lar'], rpos], '%s < %s' % (RAR, RX), leaves=leaves)
    l2 = linarith(w, A0, [r['rbr'], e['lbr'], rpos], '%s < %s' % (RX, RBR), leaves=leaves)
    l3 = linarith(w, A0, [r['iar'], e['lai'], rpos], '%s < %s' % (IAR, IX), leaves=leaves)
    l4 = linarith(w, A0, [r['ibr'], e['lbi'], rpos], '%s < %s' % (IX, IBR), leaves=leaves)
    m1 = linarith(w, A0, [r['rar'], e['lar']], 'R <_ ( %s - %s )' % (RX, RAR), leaves=leaves)
    m2 = linarith(w, A0, [r['rbr'], e['lbr']], 'R <_ ( %s - %s )' % (RBR, RX), leaves=leaves)
    m3 = linarith(w, A0, [r['iar'], e['lai']], 'R <_ ( %s - %s )' % (IX, IAR), leaves=leaves)
    m4 = linarith(w, A0, [r['ibr'], e['lbi']], 'R <_ ( %s - %s )' % (IBR, IX), leaves=leaves)
    intx = w.s([e['xc'], w.s([w.s([l1, l2], 'jca', '( %s -> ( %s < %s /\\ %s < %s ) )' % (A0, RAR, RX, RX, RBR)), w.s([l3, l4], 'jca', '( %s -> ( %s < %s /\\ %s < %s ) )' % (A0, IAR, IX, IX, IBR))], 'jca',
                               '( %s -> ( ( %s < %s /\\ %s < %s ) /\\ ( %s < %s /\\ %s < %s ) ) )' % (A0, RAR, RX, RX, RBR, IAR, IX, IX, IBR))], 'jca', '( %s -> %s )' % (A0, INTX))
    rbdx = w.s([d['rr'], w.s([w.s([m1, m2], 'jca', '( %s -> ( R <_ ( %s - %s ) /\\ R <_ ( %s - %s ) ) )' % (A0, RX, RAR, RBR, RX)), w.s([m3, m4], 'jca', '( %s -> ( R <_ ( %s - %s ) /\\ R <_ ( %s - %s ) ) )' % (A0, IX, IAR, IBR, IX))], 'jca',
                                '( %s -> ( ( R <_ ( %s - %s ) /\\ R <_ ( %s - %s ) ) /\\ ( R <_ ( %s - %s ) /\\ R <_ ( %s - %s ) ) ) )' % (A0, RX, RAR, RBR, RX, IX, IAR, IBR, IX))], 'jca', '( %s -> %s )' % (A0, RBDX))
    w.qed([intx, rbdx], 'jca', '( %s -> ( %s /\\ %s ) )' % (A0, INTX, RBDX))
    run1(w)

    # ---- holnhrm --------------------------------------------------------------------
    w = W('holnhrm', 'A point of a rectangle nested at distance R inside the domain of a holomorphic function satisfies, for some frame bound m, the standing hypotheses of the local theorems on the enlarged rectangle.')
    A0 = HAX
    han = w.s([], 'simpl', '( %s -> %s )' % (A0, HAN))
    xin = w.s([], 'simpr', '( %s -> X e. ( A crect B ) )' % A0)
    d = hanctx(w, A0, han)
    nst = w.s([w.s([w.s([d['ab'], d['Rrp']], 'jca', '( %s -> ( %s /\\ R e. RR+ ) )' % (A0, AB)), xin], 'jca', '( %s -> ( ( %s /\\ R e. RR+ ) /\\ X e. ( A crect B ) ) )' % (A0, AB)), w.inst('holnest')], 'syl',
              '( %s -> ( %s /\\ %s ) )' % (A0, INTX, RBDX))
    intx = w.s([nst, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, INTX))
    rbdx = w.s([nst, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, RBDX))
    xc = w.s([intx, w.inst('simpl')], 'syl', '( %s -> X e. CC )' % A0)
    ineq = w.s([intx, w.inst('simpr')], 'syl', '( %s -> ( ( %s < %s /\\ %s < %s ) /\\ ( %s < %s /\\ %s < %s ) ) )' % (A0, RAR, RX, RX, RBR, IAR, IX, IX, IBR))
    lt = [w.s([ineq, w.inst(rf)], 'syl', '( %s -> %s )' % (A0, f)) for rf, f in
          [('simpll', '%s < %s' % (RAR, RX)), ('simplr', '%s < %s' % (RX, RBR)), ('simprl', '%s < %s' % (IAR, IX)), ('simprr', '%s < %s' % (IX, IBR))]]
    rar = w.s([d['arc']], 'recld', '( %s -> %s e. RR )' % (A0, RAR)); iar = w.s([d['arc']], 'imcld', '( %s -> %s e. RR )' % (A0, IAR))
    rbr = w.s([d['brc']], 'recld', '( %s -> %s e. RR )' % (A0, RBR)); ibr = w.s([d['brc']], 'imcld', '( %s -> %s e. RR )' % (A0, IBR))
    rx = w.s([xc], 'recld', '( %s -> %s e. RR )' % (A0, RX)); ix = w.s([xc], 'imcld', '( %s -> %s e. RR )' % (A0, IX))
    geo = w.s([w.s([w.s([rar, rx, rbr, lt[0], lt[1]], 'lttrd', '( %s -> %s < %s )' % (A0, RAR, RBR))], 'ltled', '( %s -> %s <_ %s )' % (A0, RAR, RBR)),
               w.s([w.s([iar, ix, ibr, lt[2], lt[3]], 'lttrd', '( %s -> %s < %s )' % (A0, IAR, IBR))], 'ltled', '( %s -> %s <_ %s )' % (A0, IAR, IBR))], 'jca', '( %s -> %s )' % (A0, GEOG(AR, BR)))
    fru = w.s([d['abr'], geo, w.inst('crectfru')], 'syl2anc', '( %s -> %s C_ ( %s crect %s ) )' % (A0, FRG(AR, BR), AR, BR))
    frd = w.s([fru, d['nss']], 'sstrd', '( %s -> %s C_ D )' % (A0, FRG(AR, BR)))
    bnd = w.s([d['abr'], geo, w.s([d['fcn'], frd], 'jca', '( %s -> ( F e. ( D -cn-> CC ) /\\ %s C_ D ) )' % (A0, FRG(AR, BR))), w.inst('holfrmbd')], 'syl3anc',
              '( %s -> E. m e. RR %s )' % (A0, ALFG(AR, BR, 'm')))
    A1 = '( %s /\\ m e. RR )' % A0
    A2 = '( %s /\\ %s )' % (A1, ALFG(AR, BR, 'm'))
    rect = w.s([w.s([d['abr'], intx, d['nss']], '3jca', '( %s -> %s )' % (A0, RECTG(AR, BR, 'X')))], 'ad2antrr', '( %s -> %s )' % (A2, RECTG(AR, BR, 'X')))
    hol2 = w.s([d['hol']], 'ad2antrr', '( %s -> %s )' % (A2, HOL))
    rb0 = w.s([w.s([rbdx, d['rpos']], 'jca', '( %s -> ( %s /\\ 0 < R ) )' % (A0, RBDX))], 'ad2antrr', '( %s -> ( %s /\\ 0 < R ) )' % (A2, RBDX))
    mm = w.s([w.s([], 'simplr', '( %s -> m e. RR )' % A2), w.s([], 'simpr', '( %s -> %s )' % (A2, ALFG(AR, BR, 'm')))], 'jca', '( %s -> ( m e. RR /\\ %s ) )' % (A2, ALFG(AR, BR, 'm')))
    hrm = w.s([w.s([hol2, rect], 'jca', '( %s -> ( %s /\\ %s ) )' % (A2, HOL, RECTG(AR, BR, 'X'))), w.s([rb0, mm], 'jca', '( %s -> %s )' % (A2, RADMG(AR, BR, 'X', 'R', 'm')))], 'jca', '( %s -> %s )' % (A2, HRMX))
    rim = w.s([w.s([hrm], 'ex', '( %s -> ( %s -> %s ) )' % (A1, ALFG(AR, BR, 'm'), HRMX))], 'reximdva', '( %s -> ( E. m e. RR %s -> E. m e. RR %s ) )' % (A0, ALFG(AR, BR, 'm'), HRMX))
    w.qed([bnd, rim], 'mpd', '( %s -> E. m e. RR %s )' % (A0, HRMX))
    run1(w)

    # ---- holnid1 / holnid2 / holnfac -----------------------------------------------
    CONC1 = '( %s \\/ E. r e. RR+ %s )' % (HALFZ('X'), ISO('X', 'r'))
    w = W('holnid1', 'The dichotomy ~ holid1c at a point of a rectangle nested at distance R inside the domain: either F vanishes on the disc of radius R / 2 about the point, or the point is not a limit of zeros.')
    A0 = HAX
    ex = w.s([], 'holnhrm', '( %s -> E. m e. RR %s )' % (A0, HRMX))
    inst = w.s([w.s([], 'holid1c', '( %s -> %s )' % (HRMX, CONC1))], 'a1i', '( ( %s /\\ m e. RR ) -> ( %s -> %s ) )' % (A0, HRMX, CONC1))
    w.qed([ex, w.s([inst], 'rexlimdva', '( %s -> ( E. m e. RR %s -> %s ) )' % (A0, HRMX, CONC1))], 'mpd', '( %s -> %s )' % (A0, CONC1))
    run1(w)

    w = W('holnid2', 'The local identity theorem ~ holid2c at a point of a rectangle nested at distance R inside the domain: a holomorphic function vanishing on some disc about the point vanishes on the disc of radius R / 2 about it.')
    VANS = 'E. s e. RR+ %s' % VAN('X', 's')
    A0 = '( %s /\\ %s )' % (HAX, VANS)
    ex = w.s([w.s([], 'simpl', '( %s -> %s )' % (A0, HAX)), w.inst('holnhrm')], 'syl', '( %s -> E. m e. RR %s )' % (A0, HRMX))
    A1 = '( ( %s /\\ m e. RR ) /\\ %s )' % (A0, HRMX)
    hz = w.s([w.s([], 'simpr', '( %s -> %s )' % (A1, HRMX)), w.s([w.s([], 'simpr', '( %s -> %s )' % (A0, VANS))], 'ad2antrr', '( %s -> %s )' % (A1, VANS)), w.inst('holid2c')], 'syl2anc', '( %s -> %s )' % (A1, HALFZ('X')))
    w.qed([ex, w.s([w.s([hz], 'ex', '( ( %s /\\ m e. RR ) -> ( %s -> %s ) )' % (A0, HRMX, HALFZ('X')))], 'rexlimdva', '( %s -> ( E. m e. RR %s -> %s ) )' % (A0, HRMX, HALFZ('X')))], 'mpd', '( %s -> %s )' % (A0, HALFZ('X')))
    run1(w)

    w = W('holnfac', 'The local factorisation ~ holfacc at a point of a rectangle nested at distance R inside the domain about which F does not vanish identically.')
    NH = '-. %s' % HALFZ('X')
    A0 = '( %s /\\ %s )' % (HAX, NH)
    ex = w.s([w.s([], 'simpl', '( %s -> %s )' % (A0, HAX)), w.inst('holnhrm')], 'syl', '( %s -> E. m e. RR %s )' % (A0, HRMX))
    A1 = '( ( %s /\\ m e. RR ) /\\ %s )' % (A0, HRMX)
    fc = w.s([w.s([], 'simpr', '( %s -> %s )' % (A1, HRMX)), w.s([w.s([], 'simpr', '( %s -> %s )' % (A0, NH))], 'ad2antrr', '( %s -> %s )' % (A1, NH)), w.inst('holfacc')], 'syl2anc', '( %s -> %s )' % (A1, EXFAC('X')))
    w.qed([ex, w.s([w.s([fc], 'ex', '( ( %s /\\ m e. RR ) -> ( %s -> %s ) )' % (A0, HRMX, EXFAC('X')))], 'rexlimdva', '( %s -> ( E. m e. RR %s -> %s ) )' % (A0, HRMX, EXFAC('X')))], 'mpd', '( %s -> %s )' % (A0, EXFAC('X')))
    run1(w)
