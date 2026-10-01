"""T13: the positivity invariant of the extraction (T12's ` t12expos ` , statement ST_EXPOS of tools/gen/t12_p_srch.py):
along the pool the extraction's ` m ` stays a positive integer and the entries of ` used ` stay at least 2, because the
pool's entries are primes and the table's slots hold lists of them.

  t13tbl0    the empty table's slots are all empty, so any slot property holds (TBLPOS( EmptyTbl ))
  t13dppos   DpStep keeps TBLPOS (~ dpstepcases ): a new slot holds ` <" P "> ` or ` <" P "> ++ old ` with ` 2 <_ P `
  t13expon   one step of the invariant when the slot ` 1 mod L ` stays empty (m and used unchanged)
  t13exposs  one step when it is filled: ` m x. prodL S ` with S's entries at least 2 (~ fprodnncl ), ` S ++ used `
  t13expoi   the invariant along the pool from a generic initial state (~ nn0indd as T9's ~ exinvu )
  t12expos   the instance at ` <. 1 , <. (/) , <. EmptyTbl , (/) >. >. >. ` (T12's frozen statement)

    MM_DB=sorties/t13.mm python3 tools/gen/t13_a_pos.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t13lib import *
from t9lib import STY, ZM, ZU, ZA, ZH, ZT, DPS_, DP1, SLF, PRL, STOPB, tup_comps, vex_
from lin import linarith

SEL = sys.argv[1:]
INR = '( inr ` (/) )'
TBLPOS = lambda t: 'A. d e. NN0 ( ( %s ` d ) =/= %s -> A. q e. ran ( 2nd ` ( %s ` d ) ) 2 <_ q )' % (t, INR, t)
RAL2 = lambda u: 'A. a e. ran %s 2 <_ a' % u
Si = lambda t: '( ( W ( L ExSt N ) Z ) ` %s )' % t
NW = '( # ` W )'
PM = '( W ` m )'
AM = ZA(Si('m'))
SLM = SLF('L', PM, AM)
INV2 = lambda t: '( %s e. NN /\\ %s /\\ %s )' % (ZM(Si(t)), RAL2(ZU(Si(t))), TBLPOS(ZA(Si(t))))
T_P = ((('L e. NN', 'N e. NN0'), ('W e. Word NN0', 'Z e. %s' % STY)), RAL2('W'))
PH_P = cj(T_P)
PH_S = '( ( L e. NN /\\ N e. NN0 ) /\\ ( W e. Word NN0 /\\ Z e. %s ) )' % STY
T_C = ((T_P, 'm e. ( 0 ..^ %s )' % NW), INV2('m'))
ST_TBL0 = TBLPOS('EmptyTbl')
T_DP = (('L e. NN', 'P e. NN0', 'T e. Tbl'), ('2 <_ P', TBLPOS('T')))
ST_DPPOS = '( %s -> %s )' % (cj(T_DP), TBLPOS(DP1('L', 'P', 'T')))
ST_N = '( ( %s /\\ %s = %s ) -> %s )' % (cj(T_C), SLM, INR, INV2('( m + 1 )'))
ST_SS = '( ( %s /\\ %s =/= %s ) -> %s )' % (cj(T_C), SLM, INR, INV2('( m + 1 )'))
T_I = (T_P, ('%s e. NN' % ZM('Z'), RAL2(ZU('Z')), TBLPOS(ZA('Z'))))
ST_INV = '( ( %s /\\ I e. ( 0 ... %s ) ) -> %s )' % (cj(T_I), NW, INV2('I'))
ST_TBLPE = '( A = X -> ( %s <-> %s ) )' % (TBLPOS('A'), TBLPOS('X'))
add13s('t13tbl0', ST_TBL0)
add13s('t13tblpe', ST_TBLPE)
add13s('t13dppos', ST_DPPOS)
add13s('t13expon', ST_N)
add13s('t13exposs', ST_SS)
add13s('t13expoi', ST_INV)
add13s('t12expos', P.ST_EXPOS)


def cbv(w, ph, st, bodyv, v, target, dom):
    """( ph -> A. target e. dom body[target] ) from st : ( ph -> A. v e. dom bodyv )"""
    s = w.s
    cg = s([], 'id', '( %s = %s -> %s = %s )' % (v, target, v, target))
    sub, new = w.wcongr(bodyv, {v: target}, '%s = %s' % (v, target), {v: cg})
    bi = s([sub], 'cbvralvw', '( A. %s e. %s %s <-> A. %s e. %s %s )' % (v, dom, bodyv, target, dom, new))
    return s([st, s([bi], 'a1i', '( %s -> ( A. %s e. %s %s <-> A. %s e. %s %s ) )' % (ph, v, dom, bodyv, target, dom, new))], 'mpbid',
             '( %s -> A. %s e. %s %s )' % (ph, target, dom, new)), new


def tblpos_at(w, ph, T_, tp, d_txt, dn):
    """( ph -> ( ( T ` d_txt ) =/= inr -> A. q e. ran ( 2nd ( T ` d_txt ) ) 2 <_ q ) ) from tp : ( ph -> TBLPOS( T ) ), dn : d_txt e. NN0"""
    s = w.s
    body = lambda t: '( ( %s ` %s ) =/= %s -> A. q e. ran ( 2nd ` ( %s ` %s ) ) 2 <_ q )' % (T_, t, INR, T_, t)
    e = s([], 'id', '( d = %s -> d = %s )' % (d_txt, d_txt))
    cg, new = w.wcongr(body('d'), {'d': d_txt}, 'd = %s' % d_txt, {'d': e})
    assert new == body(d_txt), (new, body(d_txt))
    return s([cg, dn, tp], 'rspcdva', '( %s -> %s )' % (ph, body(d_txt)))


def t13tblpe():
    lab = 't13tblpe'
    w = W(lab, 'Equal tables have positive slot lists alike (the congruence of TBLPOS).')
    e = w.s([], 'id', '( A = X -> A = X )')
    st, new = w.wcongr(TBLPOS('A'), {'A': 'X'}, 'A = X', {'A': e})
    assert new == TBLPOS('X'), new
    qed13(w, st, lab)
    return w.run()


def t13tbl0():
    lab = 't13tbl0'
    w = W(lab, 'The empty table has no filled slot (~ emptytblval ), so every slot property holds of it; here the '
               'positivity of the slot lists.')
    s = w.s
    ph = 'd e. NN0'
    v = s([], 'emptytblval', '( d e. NN0 -> ( EmptyTbl ` d ) = %s )' % INR)
    # from A = B : -. A =/= B (~ nne )
    b = s([], 'nne', '( -. ( EmptyTbl ` d ) =/= %s <-> ( EmptyTbl ` d ) = %s )' % (INR, INR))
    nn = s([v, b], 'sylibr', '( d e. NN0 -> -. ( EmptyTbl ` d ) =/= %s )' % INR)
    imp = s([nn], 'pm2.21d', '( d e. NN0 -> ( ( EmptyTbl ` d ) =/= %s -> A. q e. ran ( 2nd ` ( EmptyTbl ` d ) ) 2 <_ q ) )' % INR)
    w.qed([imp], 'rgen', ST_TBL0)
    return w.run()


def t13dppos():
    lab = 't13dppos'
    ph = cj(T_DP)
    w = W(lab, 'DpStep keeps the slot lists positive (Lean\'s table invariant read for positivity): by ~ dpstepcases a filled '
               'slot of the new table is an old slot, ` <" P "> ` , or ` <" P "> ++ ` an old slot (~ ccatrn ), and ` 2 <_ P ` .')
    s = w.s
    c = Ctx(w, ph, T_DP)
    ln, pn, tt, p2, tp = c['L e. NN'], c['P e. NN0'], c['T e. Tbl'], c['2 <_ P'], c[TBLPOS('T')]
    D1 = DP1('L', 'P', 'T')
    DX = '( %s ` x )' % D1
    TX = '( T ` x )'
    G = 'A. q e. ran ( 2nd ` %s ) 2 <_ q' % DX
    pa = '( %s /\\ x e. NN0 )' % ph
    pb = '( %s /\\ %s =/= %s )' % (pa, DX, INR)
    La = lambda st: s([st], 'adantr', '( %s -> %s )' % (pa, concl(w, ph, st)))
    Lb = lambda st: s([s([st], 'adantr', '( %s -> %s )' % (pa, concl(w, ph, st)))], 'adantr', '( %s -> %s )' % (pb, concl(w, ph, st)))
    xn = s([s([], 'simpr', '( %s -> x e. NN0 )' % pa)], 'adantr', '( %s -> x e. NN0 )' % pb)
    dne = s([], 'simpr', '( %s -> %s =/= %s )' % (pb, DX, INR))
    hyp = s([s([s([Lb(ln), Lb(pn)], 'jca', '( %s -> ( L e. NN /\\ P e. NN0 ) )' % pb), Lb(tt)], 'jca', '( %s -> ( ( L e. NN /\\ P e. NN0 ) /\\ T e. Tbl ) )' % pb),
             s([xn, dne], 'jca', '( %s -> ( x e. NN0 /\\ %s =/= %s ) )' % (pb, DX, INR))], 'jca',
            '( %s -> ( ( ( L e. NN /\\ P e. NN0 ) /\\ T e. Tbl ) /\\ ( x e. NN0 /\\ %s =/= %s ) ) )' % (pb, DX, INR))
    A_ = '%s = %s' % (TX, DX)
    B_ = '( x = ( P mod L ) /\\ ( 2nd ` %s ) = <" P "> )' % DX
    BODYR = '( ( ( T ` r ) =/= %s /\\ x = ( ( r x. P ) mod L ) ) /\\ ( 2nd ` %s ) = ( <" P "> ++ ( 2nd ` ( T ` r ) ) ) )' % (INR, DX)
    C_ = 'E. r e. ( 0 ..^ L ) %s' % BODYR
    dj = s([hyp, w.inst('dpstepcases')], 'syl', '( %s -> ( %s \\/ ( %s \\/ %s ) ) )' % (pb, A_, B_, C_))
    # (a) the old slot
    p1 = '( %s /\\ %s )' % (pb, A_)
    eq = s([], 'simpr', '( %s -> %s )' % (p1, A_))
    tne = s([eq, s([dne], 'adantr', '( %s -> %s =/= %s )' % (p1, DX, INR))], 'eqnetrd', '( %s -> %s =/= %s )' % (p1, TX, INR))
    at = tblpos_at(w, p1, 'T', s([Lb(tp)], 'adantr', '( %s -> %s )' % (p1, TBLPOS('T'))), 'x', s([xn], 'adantr', '( %s -> x e. NN0 )' % p1))
    ra = s([tne, at], 'mpd', '( %s -> A. q e. ran ( 2nd ` %s ) 2 <_ q )' % (p1, TX))
    rq = s([s([s([eq], 'fveq2d', '( %s -> ( 2nd ` %s ) = ( 2nd ` %s ) )' % (p1, TX, DX))], 'rneqd', '( %s -> ran ( 2nd ` %s ) = ran ( 2nd ` %s ) )' % (p1, TX, DX))],
           'raleqdv', '( %s -> ( A. q e. ran ( 2nd ` %s ) 2 <_ q <-> %s ) )' % (p1, TX, G))
    ga = s([s([ra, rq], 'mpbid', '( %s -> %s )' % (p1, G))], 'ex', '( %s -> ( %s -> %s ) )' % (pb, A_, G))
    # (b) the singleton
    p2_ = '( %s /\\ %s )' % (pb, B_)
    e2 = s([s([], 'simpr', '( %s -> %s )' % (p2_, B_))], 'simprd', '( %s -> ( 2nd ` %s ) = <" P "> )' % (p2_, DX))
    pv = s([Lb(pn)], 'adantr', '( %s -> P e. NN0 )' % p2_)
    rn1 = s([pv, w.inst('s1rn')], 'syl', '( %s -> ran <" P "> = { P } )' % p2_)
    rn2 = s([s([e2], 'rneqd', '( %s -> ran ( 2nd ` %s ) = ran <" P "> )' % (p2_, DX)), rn1], 'eqtrd', '( %s -> ran ( 2nd ` %s ) = { P } )' % (p2_, DX))
    bq = s([], 'breq2', '( q = P -> ( 2 <_ q <-> 2 <_ P ) )')
    rs = s([bq], 'ralsng', '( P e. NN0 -> ( A. q e. { P } 2 <_ q <-> 2 <_ P ) )')
    rp = s([s([Lb(p2)], 'adantr', '( %s -> 2 <_ P )' % p2_), s([pv, rs], 'syl', '( %s -> ( A. q e. { P } 2 <_ q <-> 2 <_ P ) )' % p2_)], 'mpbird',
           '( %s -> A. q e. { P } 2 <_ q )' % p2_)
    gb = s([s([rp, s([rn2], 'raleqdv', '( %s -> ( %s <-> A. q e. { P } 2 <_ q ) )' % (p2_, G))], 'mpbird', '( %s -> %s )' % (p2_, G))], 'ex',
           '( %s -> ( %s -> %s ) )' % (pb, B_, G))
    # (c) the concatenation, under the witness r
    p3 = '( %s /\\ ( r e. ( 0 ..^ L ) /\\ %s ) )' % (pb, BODYR)
    bd = s([s([], 'simpr', '( %s -> ( r e. ( 0 ..^ L ) /\\ %s ) )' % (p3, BODYR))], 'simprd', '( %s -> %s )' % (p3, BODYR))
    rin = s([s([], 'simpr', '( %s -> ( r e. ( 0 ..^ L ) /\\ %s ) )' % (p3, BODYR))], 'simpld', '( %s -> r e. ( 0 ..^ L ) )' % p3)
    rn0 = s([rin, w.inst('elfzonn0')], 'syl', '( %s -> r e. NN0 )' % p3)
    rne = s([s([bd], 'simpld', '( %s -> ( ( T ` r ) =/= %s /\\ x = ( ( r x. P ) mod L ) ) )' % (p3, INR))], 'simpld', '( %s -> ( T ` r ) =/= %s )' % (p3, INR))
    e3 = s([bd], 'simprd', '( %s -> ( 2nd ` %s ) = ( <" P "> ++ ( 2nd ` ( T ` r ) ) ) )' % (p3, DX))
    L3 = lambda st: s([Lb(st)], 'adantr', '( %s -> %s )' % (p3, concl(w, ph, st)))
    atr = tblpos_at(w, p3, 'T', L3(tp), 'r', rn0)
    rar = s([rne, atr], 'mpd', '( %s -> A. q e. ran ( 2nd ` ( T ` r ) ) 2 <_ q )' % p3)
    trw = s([s([s([L3(tt), rn0], 'jca', '( %s -> ( T e. Tbl /\\ r e. NN0 ) )' % p3), rne], 'jca', '( %s -> ( ( T e. Tbl /\\ r e. NN0 ) /\\ ( T ` r ) =/= %s ) )' % (p3, INR)),
             w.inst('tblpay')], 'syl', '( %s -> ( ( 2nd ` ( T ` r ) ) e. Word NN0 /\\ ( T ` r ) = ( inl ` ( 2nd ` ( T ` r ) ) ) ) )' % p3)
    trw1 = s([trw], 'simpld', '( %s -> ( 2nd ` ( T ` r ) ) e. Word NN0 )' % p3)
    s1w = s([L3(pn)], 's1cld', '( %s -> <" P "> e. Word NN0 )' % p3)
    cr = s([s1w, trw1, w.inst('ccatrn')], 'syl2anc', '( %s -> ran ( <" P "> ++ ( 2nd ` ( T ` r ) ) ) = ( ran <" P "> u. ran ( 2nd ` ( T ` r ) ) ) )' % p3)
    rn1c = s([L3(pn), w.inst('s1rn')], 'syl', '( %s -> ran <" P "> = { P } )' % p3)
    rpc = s([L3(p2), s([L3(pn), rs], 'syl', '( %s -> ( A. q e. { P } 2 <_ q <-> 2 <_ P ) )' % p3)], 'mpbird', '( %s -> A. q e. { P } 2 <_ q )' % p3)
    rp1 = s([rpc, s([rn1c], 'raleqdv', '( %s -> ( A. q e. ran <" P "> 2 <_ q <-> A. q e. { P } 2 <_ q ) )' % p3)], 'mpbird', '( %s -> A. q e. ran <" P "> 2 <_ q )' % p3)
    un = s([s([rp1, rar], 'jca', '( %s -> ( A. q e. ran <" P "> 2 <_ q /\\ A. q e. ran ( 2nd ` ( T ` r ) ) 2 <_ q ) )' % p3),
            s([], 'ralunb', '( A. q e. ( ran <" P "> u. ran ( 2nd ` ( T ` r ) ) ) 2 <_ q <-> ( A. q e. ran <" P "> 2 <_ q /\\ A. q e. ran ( 2nd ` ( T ` r ) ) 2 <_ q ) )')],
           'sylibr', '( %s -> A. q e. ( ran <" P "> u. ran ( 2nd ` ( T ` r ) ) ) 2 <_ q )' % p3)
    rq3 = s([s([e3], 'rneqd', '( %s -> ran ( 2nd ` %s ) = ran ( <" P "> ++ ( 2nd ` ( T ` r ) ) ) )' % (p3, DX)), cr], 'eqtrd',
             '( %s -> ran ( 2nd ` %s ) = ( ran <" P "> u. ran ( 2nd ` ( T ` r ) ) ) )' % (p3, DX))
    g3 = s([un, s([rq3], 'raleqdv', '( %s -> ( %s <-> A. q e. ( ran <" P "> u. ran ( 2nd ` ( T ` r ) ) ) 2 <_ q ) )' % (p3, G))], 'mpbird', '( %s -> %s )' % (p3, G))
    gc = s([g3], 'rexlimdvaa', '( %s -> ( %s -> %s ) )' % (pb, C_, G))
    gbc = s([gb, gc], 'jaod', '( %s -> ( ( %s \\/ %s ) -> %s ) )' % (pb, B_, C_, G))
    gabc = s([ga, gbc], 'jaod', '( %s -> ( ( %s \\/ ( %s \\/ %s ) ) -> %s ) )' % (pb, A_, B_, C_, G))
    g = s([dj, gabc], 'mpd', '( %s -> %s )' % (pb, G))
    imp = s([g], 'ex', '( %s -> ( %s =/= %s -> %s ) )' % (pa, DX, INR, G))
    ral = s([imp], 'ralrimiva', '( %s -> A. x e. NN0 ( %s =/= %s -> %s ) )' % (ph, DX, INR, G))
    fin, new = cbv(w, ph, ral, '( %s =/= %s -> %s )' % (DX, INR, G), 'x', 'd', 'NN0')
    assert new == '( ( %s ` d ) =/= %s -> A. q e. ran ( 2nd ` ( %s ` d ) ) 2 <_ q )' % (D1, INR, D1), new
    qed13(w, fin, lab)
    return w.run()


class Stp:
    """the facts of a step lemma under ph (the tree T_C plus the case)"""
    def __init__(self, w, ph, T):
        s = w.s
        self.w, self.ph = w, ph
        c = Ctx(w, ph, T)
        self.c = c
        self.ln, self.nn, self.ww, self.zs = c['L e. NN'], c['N e. NN0'], c['W e. Word NN0'], c['Z e. %s' % STY]
        self.wal = c[RAL2('W')]
        mo = c['m e. ( 0 ..^ %s )' % NW]
        self.mz = s([mo, w.inst('elfzofz')], 'syl', '( %s -> m e. ( 0 ... %s ) )' % (ph, NW))
        self.mn = s([mo, w.inst('elfzonn0')], 'syl', '( %s -> m e. NN0 )' % ph)
        self.ps = s([s([self.ln, self.nn], 'jca', '( %s -> ( L e. NN /\\ N e. NN0 ) )' % ph),
                     s([self.ww, self.zs], 'jca', '( %s -> ( W e. Word NN0 /\\ Z e. %s ) )' % (ph, STY))], 'jca', '( %s -> %s )' % (ph, PH_S))
        psm = s([self.ps, self.mz], 'jca', '( %s -> ( %s /\\ m e. ( 0 ... %s ) ) )' % (ph, PH_S, NW))
        self.sm = s([psm, w.inst('exstcl')], 'syl', '( %s -> %s e. %s )' % (ph, Si('m'), STY))
        self.pmn = s([self.ww, mo, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, PM))
        wr = s([s([self.ww, w.inst('wrdfn')], 'syl', '( %s -> W Fn ( 0 ..^ %s ) )' % (ph, NW)), mo, w.inst('fnfvelrn')], 'syl2anc',
               '( %s -> %s e. ran W )' % (ph, PM))
        self.pm2 = s([s([], 'breq2', '( a = %s -> ( 2 <_ a <-> 2 <_ %s ) )' % (PM, PM)), wr, self.wal], 'rspcdva', '( %s -> 2 <_ %s )' % (ph, PM))
        T23 = '( Word NN0 X. ( Tbl X. 2o ) )'
        sm = self.sm
        self.mm = s([sm, w.inst('xp1st')], 'syl', '( %s -> %s e. NN0 )' % (ph, ZM(Si('m'))))
        z2 = s([sm, w.inst('xp2nd')], 'syl', '( %s -> ( 2nd ` %s ) e. %s )' % (ph, Si('m'), T23))
        self.um = s([z2, w.inst('xp1st')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, ZU(Si('m'))))
        z3 = s([z2, w.inst('xp2nd')], 'syl', '( %s -> ( 2nd ` ( 2nd ` %s ) ) e. ( Tbl X. 2o ) )' % (ph, Si('m')))
        self.am = s([z3, w.inst('xp1st')], 'syl', '( %s -> %s e. Tbl )' % (ph, AM))
        dp = s([s([s([self.ln, self.pmn], 'jca', '( %s -> ( L e. NN /\\ %s e. NN0 ) )' % (ph, PM)), self.am], 'jca',
                  '( %s -> ( ( L e. NN /\\ %s e. NN0 ) /\\ %s e. Tbl ) )' % (ph, PM, AM)), w.inst('dpstepcl')], 'syl',
               '( %s -> %s e. ( Tbl X. NN0 ) )' % (ph, DPS_('L', PM, AM)))
        self.a1 = s([dp, w.inst('xp1st')], 'syl', '( %s -> %s e. Tbl )' % (ph, DP1('L', PM, AM)))
        inv = c[INV2('m')]
        self.mpos = s([inv], 'simp1d', '( %s -> %s e. NN )' % (ph, ZM(Si('m'))))
        self.ralu = s([inv], 'simp2d', '( %s -> %s )' % (ph, RAL2(ZU(Si('m')))))
        self.tbm = s([inv], 'simp3d', '( %s -> %s )' % (ph, TBLPOS(AM)))
        # the new table's positivity
        self.tb1 = s([s([s([self.ln, self.pmn, self.am], '3jca', '( %s -> ( L e. NN /\\ %s e. NN0 /\\ %s e. Tbl ) )' % (ph, PM, AM)),
                         s([self.pm2, self.tbm], 'jca', '( %s -> ( 2 <_ %s /\\ %s ) )' % (ph, PM, TBLPOS(AM)))], 'jca',
                        '( %s -> ( ( L e. NN /\\ %s e. NN0 /\\ %s e. Tbl ) /\\ ( 2 <_ %s /\\ %s ) ) )' % (ph, PM, AM, PM, TBLPOS(AM))),
                      w.inst('t13dppos')], 'syl', '( %s -> %s )' % (ph, TBLPOS(DP1('L', PM, AM))))
        # the next state
        sp = s([s([self.ps, self.mn], 'jca', '( %s -> ( %s /\\ m e. NN0 ) )' % (ph, PH_S)), w.inst('exstp1')], 'syl',
               '( %s -> %s = ( %s ( L ExStOp N ) %s ) )' % (ph, Si('( m + 1 )'), Si('m'), PM))
        ov = s([s([s([self.ln, self.nn], 'jca', '( %s -> ( L e. NN /\\ N e. NN0 ) )' % ph), s([sm, self.pmn], 'jca',
                  '( %s -> ( %s e. %s /\\ %s e. NN0 ) )' % (ph, Si('m'), STY, PM))], 'jca',
                  '( %s -> ( ( L e. NN /\\ N e. NN0 ) /\\ ( %s e. %s /\\ %s e. NN0 ) ) )' % (ph, Si('m'), STY, PM)), w.inst('exstopv')], 'syl',
               '( %s -> ( %s ( L ExStOp N ) %s ) = %s )' % (ph, Si('m'), PM, STOPB('L', 'N', Si('m'), PM)))
        self.nxt = s([sp, ov], 'eqtrd', '( %s -> %s = %s )' % (ph, Si('( m + 1 )'), STOPB('L', 'N', Si('m'), PM)))

    def finish(self, zp, m_, u_, a_, mpos_, ral_, tbb_):
        """INV2( m + 1 ) from the component facts about the next state's m used table"""
        w, ph, s = self.w, self.ph, self.w.s
        S1 = Si('( m + 1 )')
        em, eu, ea = zp['m'], zp['u'], zp['a']
        mp = s([em, mpos_], 'eqeltrd', '( %s -> %s e. NN )' % (ph, ZM(S1)))
        rl = s([ral_, s([s([eu], 'rneqd', '( %s -> ran %s = ran %s )' % (ph, ZU(S1), u_))], 'raleqdv', '( %s -> ( %s <-> %s ) )' % (ph, RAL2(ZU(S1)), RAL2(u_)))],
               'mpbird', '( %s -> %s )' % (ph, RAL2(ZU(S1))))
        tb = s([tbb_, s([ea, w.inst('t13tblpe')], 'syl', '( %s -> ( %s <-> %s ) )' % (ph, TBLPOS(ZA(S1)), TBLPOS(a_)))], 'mpbird', '( %s -> %s )' % (ph, TBLPOS(ZA(S1))))
        return s([mp, rl, tb], '3jca', '( %s -> %s )' % (ph, INV2('( m + 1 )')))


def t13expon():
    lab = 't13expon'
    T = (T_C, '%s = %s' % (SLM, INR))
    ph = cj(T)
    w = W(lab, 'One step of the positivity invariant of the extraction when the slot ` 1 mod L ` of the new table stays '
               'empty: ` m ` and ` used ` are unchanged and the table stays positive (~ t13dppos ).')
    s = w.s
    X = Stp(w, ph, T)
    c = X.c
    A1 = DP1('L', PM, AM)
    T1 = ZT(ZM(Si('m')), ZU(Si('m')), A1, '(/)')
    it = s([c['%s = %s' % (SLM, INR)]], 'iftrued', '( %s -> %s = %s )' % (ph, STOPB('L', 'N', Si('m'), PM), T1))
    zeq = s([X.nxt, it], 'eqtrd', '( %s -> %s = %s )' % (ph, Si('( m + 1 )'), T1))
    vex = {'m': vex_(w, ph, ZM(Si('m'))), 'u': vex_(w, ph, ZU(Si('m'))), 'a': vex_(w, ph, A1), 'h': vex_(w, ph, '(/)')}
    zp = tup_comps(w, ph, Si('( m + 1 )'), zeq, ZM(Si('m')), ZU(Si('m')), A1, '(/)', vex)
    inv = X.finish(zp, ZM(Si('m')), ZU(Si('m')), A1, X.mpos, X.ralu, X.tb1)
    qed13(w, inv, lab)
    return w.run()


def t13exposs():
    lab = 't13exposs'
    T = (T_C, '%s =/= %s' % (SLM, INR))
    ph = cj(T)
    w = W(lab, 'One step of the positivity invariant of the extraction when the slot ` 1 mod L ` of the new table holds a '
               'witness list ` S ` : its entries are at least 2 (~ t13dppos ), so ` prodL S ` is a positive integer '
               '(~ prodlspec , ~ fprodnncl ) and ` m x. prodL S ` stays positive; ` S ++ used ` keeps the entries at least 2 '
               '(~ ccatrn ); the table is reset to the empty one (~ t13tbl0 ).')
    s = w.s
    X = Stp(w, ph, T)
    c = X.c
    A1 = DP1('L', PM, AM)
    WV = '( 2nd ` %s )' % SLM
    MM = '( %s x. %s )' % (ZM(Si('m')), PRL(WV))
    WU = '( %s ++ %s )' % (WV, ZU(Si('m')))
    HT = 'if ( N < %s , 1o , (/) )' % MM
    T2 = ZT(MM, WU, 'EmptyTbl', HT)
    nn = c['%s =/= %s' % (SLM, INR)]
    it = s([s([nn], 'neneqd', '( %s -> -. %s = %s )' % (ph, SLM, INR))], 'iffalsed', '( %s -> %s = %s )' % (ph, STOPB('L', 'N', Si('m'), PM), T2))
    zeq = s([X.nxt, it], 'eqtrd', '( %s -> %s = %s )' % (ph, Si('( m + 1 )'), T2))
    hv = s([s([s([], '1oex', '1o e. _V'), s([], '0ex', '(/) e. _V')], 'ifex', '%s e. _V' % HT)], 'a1i', '( %s -> %s e. _V )' % (ph, HT))
    vex = {'m': vex_(w, ph, MM), 'u': vex_(w, ph, WU), 'a': vex_(w, ph, 'EmptyTbl'), 'h': hv}
    zp = tup_comps(w, ph, Si('( m + 1 )'), zeq, MM, WU, 'EmptyTbl', HT, vex)
    # the witness list: a word with entries at least 2
    ML = '( 1 mod L )'
    mln = s([closed(w, ph, '1z', '1 e. ZZ'), X.ln, w.inst('zmodcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, ML))
    at = tblpos_at(w, ph, A1, X.tb1, ML, mln)
    wq = s([nn, at], 'mpd', '( %s -> A. q e. ran %s 2 <_ q )' % (ph, WV))
    wvw = s([s([s([s([X.a1, mln], 'jca', '( %s -> ( %s e. Tbl /\\ %s e. NN0 ) )' % (ph, A1, ML)), nn], 'jca',
                  '( %s -> ( ( %s e. Tbl /\\ %s e. NN0 ) /\\ %s =/= %s ) )' % (ph, A1, ML, SLM, INR)), w.inst('tblpay')], 'syl',
               '( %s -> ( %s e. Word NN0 /\\ %s = ( inl ` %s ) ) )' % (ph, WV, SLM, WV))], 'simpld', '( %s -> %s e. Word NN0 )' % (ph, WV))
    # prodL WV e. NN
    LWV = '( # ` %s )' % WV
    pr = s([wvw, w.inst('prodlspec')], 'syl', '( %s -> %s = prod_ i e. ( 0 ..^ %s ) ( %s ` i ) )' % (ph, PRL(WV), LWV, WV))
    fin_ = s([s([], 'fzofi', '( 0 ..^ %s ) e. Fin' % LWV)], 'a1i', '( %s -> ( 0 ..^ %s ) e. Fin )' % (ph, LWV))
    pi = '( %s /\\ i e. ( 0 ..^ %s ) )' % (ph, LWV)
    ii = s([], 'simpr', '( %s -> i e. ( 0 ..^ %s ) )' % (pi, LWV))
    wvi = s([wvw], 'adantr', '( %s -> %s e. Word NN0 )' % (pi, WV))
    vin = s([wvi, ii, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> ( %s ` i ) e. NN0 )' % (pi, WV))
    vrn = s([s([wvi, w.inst('wrdfn')], 'syl', '( %s -> %s Fn ( 0 ..^ %s ) )' % (pi, WV, LWV)), ii, w.inst('fnfvelrn')], 'syl2anc',
            '( %s -> ( %s ` i ) e. ran %s )' % (pi, WV, WV))
    v2 = s([s([], 'breq2', '( q = ( %s ` i ) -> ( 2 <_ q <-> 2 <_ ( %s ` i ) ) )' % (WV, WV)), vrn, s([wq], 'adantr', '( %s -> A. q e. ran %s 2 <_ q )' % (pi, WV))],
           'rspcdva', '( %s -> 2 <_ ( %s ` i ) )' % (pi, WV))
    cli = Closure(w, pi, {'( %s ` i )' % WV: ('NN0', vin)})
    v1 = linarith(w, pi, [v2], '1 <_ ( %s ` i )' % WV, closure=cli)
    vnn = s([s([vin, v1], 'jca', '( %s -> ( ( %s ` i ) e. NN0 /\\ 1 <_ ( %s ` i ) ) )' % (pi, WV, WV)), w.inst('elnnnn0c')], 'sylibr',
            '( %s -> ( %s ` i ) e. NN )' % (pi, WV))
    fp = s([fin_, vnn], 'fprodnncl', '( %s -> prod_ i e. ( 0 ..^ %s ) ( %s ` i ) e. NN )' % (ph, LWV, WV))
    prn = s([pr, fp], 'eqeltrd', '( %s -> %s e. NN )' % (ph, PRL(WV)))
    mmn = s([X.mpos, prn], 'nnmulcld', '( %s -> %s e. NN )' % (ph, MM))
    # used: ran ( WV ++ used ) = ran WV u. ran used
    wa, _ = cbv(w, ph, wq, '2 <_ q', 'q', 'a', 'ran %s' % WV)
    cr = s([wvw, X.um, w.inst('ccatrn')], 'syl2anc', '( %s -> ran %s = ( ran %s u. ran %s ) )' % (ph, WU, WV, ZU(Si('m'))))
    ru = s([s([wa, X.ralu], 'jca', '( %s -> ( %s /\\ %s ) )' % (ph, RAL2(WV), RAL2(ZU(Si('m'))))),
            s([], 'ralunb', '( A. a e. ( ran %s u. ran %s ) 2 <_ a <-> ( %s /\\ %s ) )' % (WV, ZU(Si('m')), RAL2(WV), RAL2(ZU(Si('m')))))],
           'sylibr', '( %s -> A. a e. ( ran %s u. ran %s ) 2 <_ a )' % (ph, WV, ZU(Si('m'))))
    rq = s([ru, s([cr], 'raleqdv', '( %s -> ( %s <-> A. a e. ( ran %s u. ran %s ) 2 <_ a ) )' % (ph, RAL2(WU), WV, ZU(Si('m'))))], 'mpbird',
           '( %s -> %s )' % (ph, RAL2(WU)))
    tb0 = closed(w, ph, 't13tbl0', ST_TBL0)
    inv = X.finish(zp, MM, WU, 'EmptyTbl', mmn, rq, tb0)
    qed13(w, inv, lab)
    return w.run()


def t13expoi():
    lab = 't13expoi'
    ph = cj(T_I)
    w = W(lab, 'The positivity invariant of the extraction along the pool from a generic initial state (induction as '
               'T9\'s ~ exinvu ): ` m ` stays a positive integer, the entries of ` used ` stay at least 2, the table\'s '
               'slot lists stay positive (~ t13expon , ~ t13exposs ).')
    s = w.s
    c = Ctx(w, ph, T_I)
    ln, nn, ww, zs = c['L e. NN'], c['N e. NN0'], c['W e. Word NN0'], c['Z e. %s' % STY]
    ps0 = s([s([ln, nn], 'jca', '( %s -> ( L e. NN /\\ N e. NN0 ) )' % ph), s([ww, zs], 'jca', '( %s -> ( W e. Word NN0 /\\ Z e. %s ) )' % (ph, STY))],
            'jca', '( %s -> %s )' % (ph, PH_S))
    PS = lambda t: '( %s <_ %s -> %s )' % (t, NW, INV2(t))

    def sb(b):
        e = s([], 'id', '( n = %s -> n = %s )' % (b, b))
        st, new = w.wcongr(PS('n'), {'n': b}, 'n = %s' % b, {'n': e})
        assert new == PS(b), new
        return st
    h1, h2, h3, h4 = sb('0'), sb('m'), sb('( m + 1 )'), sb('I')
    # base
    S0 = Si('0')
    z0 = s([ps0, w.inst('exst0')], 'syl', '( %s -> %s = Z )' % (ph, S0))
    f2 = s([z0], 'fveq2d', '( %s -> ( 2nd ` %s ) = ( 2nd ` Z ) )' % (ph, S0))
    eu = s([f2], 'fveq2d', '( %s -> %s = %s )' % (ph, ZU(S0), ZU('Z')))
    ea = s([s([f2], 'fveq2d', '( %s -> ( 2nd ` ( 2nd ` %s ) ) = ( 2nd ` ( 2nd ` Z ) ) )' % (ph, S0))], 'fveq2d', '( %s -> %s = %s )' % (ph, ZA(S0), ZA('Z')))
    em = s([z0], 'fveq2d', '( %s -> %s = %s )' % (ph, ZM(S0), ZM('Z')))
    m0 = s([em, c['%s e. NN' % ZM('Z')]], 'eqeltrd', '( %s -> %s e. NN )' % (ph, ZM(S0)))
    r0 = s([c[RAL2(ZU('Z'))], s([s([eu], 'rneqd', '( %s -> ran %s = ran %s )' % (ph, ZU(S0), ZU('Z')))], 'raleqdv', '( %s -> ( %s <-> %s ) )' % (ph, RAL2(ZU(S0)), RAL2(ZU('Z'))))],
           'mpbird', '( %s -> %s )' % (ph, RAL2(ZU(S0))))
    t0 = s([c[TBLPOS(ZA('Z'))], s([ea, w.inst('t13tblpe')], 'syl', '( %s -> ( %s <-> %s ) )' % (ph, TBLPOS(ZA(S0)), TBLPOS(ZA('Z'))))], 'mpbird', '( %s -> %s )' % (ph, TBLPOS(ZA(S0))))
    base = s([s([m0, r0, t0], '3jca', '( %s -> %s )' % (ph, INV2('0')))], 'a1d', '( %s -> %s )' % (ph, PS('0')))
    # step
    a = '( ( %s /\\ m e. NN0 ) /\\ %s )' % (ph, PS('m'))
    a2 = '( %s /\\ ( m + 1 ) <_ %s )' % (a, NW)
    La = lambda st: s([s([s([st], 'adantr', '( ( %s /\\ m e. NN0 ) -> %s )' % (ph, concl(w, ph, st)))], 'adantr', '( %s -> %s )' % (a, concl(w, ph, st)))],
                      'adantr', '( %s -> %s )' % (a2, concl(w, ph, st)))
    mn = s([s([], 'simplr', '( %s -> m e. NN0 )' % a)], 'adantr', '( %s -> m e. NN0 )' % a2)
    ih0 = s([s([], 'simpr', '( %s -> %s )' % (a, PS('m')))], 'adantr', '( %s -> %s )' % (a2, PS('m')))
    m1l = s([], 'simpr', '( %s -> ( m + 1 ) <_ %s )' % (a2, NW))
    lw = s([La(ww), w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (a2, NW))
    cla = Closure(w, a2, {'m': ('NN0', mn), NW: ('NN0', lw)})
    mle = linarith(w, a2, [m1l], 'm <_ %s' % NW, closure=cla)
    ih = s([mle, ih0], 'mpd', '( %s -> %s )' % (a2, INV2('m')))
    mlt = linarith(w, a2, [m1l], 'm < %s' % NW, closure=cla)
    posw = linarith(w, a2, [m1l, cla.ge0('m')], '0 < %s' % NW, closure=cla)
    wnn = s([s([lw, posw], 'jca', '( %s -> ( %s e. NN0 /\\ 0 < %s ) )' % (a2, NW, NW)), w.inst('elnnnn0b')], 'sylibr', '( %s -> %s e. NN )' % (a2, NW))
    mo = s([s([mn, wnn, mlt], '3jca', '( %s -> ( m e. NN0 /\\ %s e. NN /\\ m < %s ) )' % (a2, NW, NW)), w.inst('elfzo0')], 'sylibr',
           '( %s -> m e. ( 0 ..^ %s ) )' % (a2, NW))
    tp = s([s([La(ln), La(nn)], 'jca', '( %s -> ( L e. NN /\\ N e. NN0 ) )' % a2), s([La(ww), La(zs)], 'jca', '( %s -> ( W e. Word NN0 /\\ Z e. %s ) )' % (a2, STY))],
           'jca', '( %s -> %s )' % (a2, PH_S))
    tpp = s([tp, La(c[RAL2('W')])], 'jca', '( %s -> %s )' % (a2, PH_P))
    tc = s([s([tpp, mo], 'jca', '( %s -> ( %s /\\ m e. ( 0 ..^ %s ) ) )' % (a2, PH_P, NW)), ih], 'jca', '( %s -> %s )' % (a2, cj(T_C)))
    cn_ = s([s([], 't13expon', ST_N)], 'ex', '( %s -> ( %s = %s -> %s ) )' % (cj(T_C), SLM, INR, INV2('( m + 1 )')))
    cs_ = s([s([], 't13exposs', ST_SS)], 'ex', '( %s -> ( %s =/= %s -> %s ) )' % (cj(T_C), SLM, INR, INV2('( m + 1 )')))
    cases = s([cn_, cs_], 'pm2.61dne', '( %s -> %s )' % (cj(T_C), INV2('( m + 1 )')))
    q2 = s([tc, cases], 'syl', '( %s -> %s )' % (a2, INV2('( m + 1 )')))
    st = s([q2], 'ex', '( %s -> %s )' % (a, PS('( m + 1 )')))
    ind = s([h1, h2, h3, h4, base, st], 'nn0indd', '( ( %s /\\ I e. NN0 ) -> %s )' % (ph, PS('I')))
    p = '( %s /\\ I e. ( 0 ... %s ) )' % (ph, NW)
    ifz = s([], 'simpr', '( %s -> I e. ( 0 ... %s ) )' % (p, NW))
    inn = s([ifz, w.inst('elfznn0')], 'syl', '( %s -> I e. NN0 )' % p)
    ile = s([ifz, w.inst('elfzle2')], 'syl', '( %s -> I <_ %s )' % (p, NW))
    i2 = s([s([s([], 'simpl', '( %s -> %s )' % (p, ph)), inn], 'jca', '( %s -> ( %s /\\ I e. NN0 ) )' % (p, ph)), ind], 'syl', '( %s -> %s )' % (p, PS('I')))
    fin = s([ile, i2], 'mpd', '( %s -> %s )' % (p, INV2('I')))
    qed13(w, fin, lab)
    return w.run()


def t12expos():
    lab = 't12expos'
    Z0 = P.Z0
    T = ((('L e. NN', 'N e. NN0'), ('W e. Word NN0', RAL2('W'))), 'I e. ( 0 ... %s )' % NW)
    ph = cj(T)
    w = W(lab, 'The extraction keeps ` m ` positive and the entries of ` used ` at least 2 (Lean\'s positivity read by '
               'Step5 for ` verifyF_le_B ` ): ~ t13expoi at the initial state ` ( 1 , [] , emptyTbl , false ) ` .')
    s = w.s
    c = Ctx(w, ph, T)
    ln, nn, ww, wal, ii = c['L e. NN'], c['N e. NN0'], c['W e. Word NN0'], c[RAL2('W')], c['I e. ( 0 ... %s )' % NW]
    z0 = P.z0_in_sty(w, ph)
    p1, p2, p3, p4 = P.z0_parts(w, ph)
    m1 = s([p1, closed(w, ph, '1nn', '1 e. NN')], 'eqeltrd', '( %s -> %s e. NN )' % (ph, ZM(Z0)))
    r0 = s([s([s([s([], 'rn0', 'ran (/) = (/)')], 'raleqi', '( A. a e. ran (/) 2 <_ a <-> A. a e. (/) 2 <_ a )'), s([], 'ral0', 'A. a e. (/) 2 <_ a')], 'mpbir',
              'A. a e. ran (/) 2 <_ a')], 'a1i', '( %s -> A. a e. ran (/) 2 <_ a )' % ph)
    rz = s([r0, s([s([p2], 'rneqd', '( %s -> ran %s = ran (/) )' % (ph, ZU(Z0)))], 'raleqdv', '( %s -> ( %s <-> A. a e. ran (/) 2 <_ a ) )' % (ph, RAL2(ZU(Z0))))],
           'mpbird', '( %s -> %s )' % (ph, RAL2(ZU(Z0))))
    tz = s([closed(w, ph, 't13tbl0', ST_TBL0), s([p3, w.inst('t13tblpe')], 'syl', '( %s -> ( %s <-> %s ) )' % (ph, TBLPOS(ZA(Z0)), ST_TBL0))], 'mpbird', '( %s -> %s )' % (ph, TBLPOS(ZA(Z0))))
    m = {'Z': Z0}
    ex = {'L e. NN': ln, 'N e. NN0': nn, 'W e. Word NN0': ww, '%s e. %s' % (Z0, STY): z0, RAL2('W'): wal, '%s e. NN' % ZM(Z0): m1, RAL2(ZU(Z0)): rz,
          TBLPOS(ZA(Z0)): tz, 'I e. ( 0 ... %s )' % NW: ii}
    st, cc = inst(w, ph, 't13expoi', m, Bld(w, ph, c, ex))
    fin = s([s([st], 'simp1d', '( %s -> %s e. NN )' % (ph, P.MI('I'))), s([st], 'simp2d', '( %s -> %s )' % (ph, RAL2(P.UI('I'))))], 'jca',
            '( %s -> ( %s e. NN /\\ %s ) )' % (ph, P.MI('I'), RAL2(P.UI('I'))))
    qed13(w, fin, lab)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
