"""T8b: setIfNoneF at the table level (Lean ` setIfNoneF_tbl ` ) and its word lemmas.

  ttsetfv   the values of ( ( A SetIfNone J ) ` W ) (Lean ` Alg.setIfNone ` , ` Function.update ` )
  ttwsplit  a word is its prefix, its letter at J and its rest (Lean ` List.drop_eq_getElem_cons ` )
  ttsetsl   the first L slots of ( ( A SetIfNone J ) ` W ) are Lean's ` setSlotL ` of the first L slots
            of A (Lean ` map_range_setIfNone ` , ` setSlotL_eq_take_cons_drop ` )
  tmisint   setIfNoneF_tbl

    MM_DB=sorties/t8b.mm python3 tools/gen/t8b_j_set.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t8blib import *
from lin import linarith
from t8b_h_tbl import tbl_prep

SEL = sys.argv[1:]
NONE_ = '( inr ` (/) )'
AP = '( ( A SetIfNone J ) ` W )'
FILLA = 'if ( ( A ` J ) = %s , ( inl ` W ) , ( A ` J ) )' % NONE_
UPDT = '( ( A |` ( NN0 \\ { J } ) ) u. { <. J , ( inl ` W ) >. } )'
ST_FV = ('( ( ( A e. Tbl /\\ J e. NN0 /\\ W e. Word NN0 ) /\\ I e. NN0 ) -> ( %s ` I ) = if ( I = J , %s , ( A ` I ) ) )'
         % (AP, FILLA))
ST_SPL = ('( ( V e. Word S /\\ J e. ( 0 ..^ ( # ` V ) ) ) -> V = ( ( V prefix J ) ++ ( <" ( V ` J ) "> ++ '
          '( V substr <. ( J + 1 ) , ( # ` V ) >. ) ) ) )')
WL = '( A |` ( 0 ..^ L ) )'
WLP = '( %s |` ( 0 ..^ L ) )' % AP
FILLW = 'if ( ( %s ` J ) = %s , ( inl ` W ) , ( %s ` J ) )' % (WL, NONE_, WL)
SSLJ = '( ( %s prefix J ) ++ ( <" %s "> ++ ( %s substr <. ( J + 1 ) , ( # ` %s ) >. ) ) )' % (WL, FILLW, WL, WL)
PH_SL = '( ( A e. Tbl /\\ L e. NN0 ) /\\ ( J e. NN0 /\\ J < L /\\ W e. Word NN0 ) )'
ST_SL = '( %s -> %s = %s )' % (PH_SL, WLP, SSLJ)


def ttsetfv():
    ph = '( ( A e. Tbl /\\ J e. NN0 /\\ W e. Word NN0 ) /\\ I e. NN0 )'
    w = W('ttsetfv', 'The values of the guarded table write: slot ` J ` is filled with ` W ` if it was empty, every '
                     'other slot kept (Lean ` Alg.setIfNone ` , ` Function.update_self ` , ` Function.update_of_ne ` ).')
    s = w.s
    a3 = s([], 'simpl', '( %s -> ( A e. Tbl /\\ J e. NN0 /\\ W e. Word NN0 ) )' % ph)
    at = s([a3], 'simp1d', '( %s -> A e. Tbl )' % ph)
    jn = s([a3], 'simp2d', '( %s -> J e. NN0 )' % ph)
    ww = s([a3], 'simp3d', '( %s -> W e. Word NN0 )' % ph)
    inn = s([], 'simpr', '( %s -> I e. NN0 )' % ph)
    C1 = '( A ` J ) = %s' % NONE_
    sv = s([s([at, jn], 'jca', '( %s -> ( A e. Tbl /\\ J e. NN0 ) )' % ph), ww, w.inst('setifnoneval')], 'syl2anc',
           '( %s -> %s = if ( %s , %s , A ) )' % (ph, AP, C1, UPDT))
    RHS = 'if ( I = J , %s , ( A ` I ) )' % FILLA
    GOAL = lambda p: '( %s -> ( %s ` I ) = %s )' % (p, AP, RHS)
    L = lambda p, st, base=ph: s([st], 'adantr', '( %s -> %s )' % (p, concl(w, base, st)))
    # case A ` J = none
    p1 = '( %s /\\ %s )' % (ph, C1)
    c1 = s([], 'simpr', '( %s -> %s )' % (p1, C1))
    e1 = s([L(p1, sv), s([c1], 'iftrued', '( %s -> if ( %s , %s , A ) = %s )' % (p1, C1, UPDT, UPDT))], 'eqtrd', '( %s -> %s = %s )' % (p1, AP, UPDT))
    f1 = s([e1], 'fveq1d', '( %s -> ( %s ` I ) = ( %s ` I ) )' % (p1, AP, UPDT))
    #   I = J
    p11 = '( %s /\\ I = J )' % p1
    ij = s([], 'simpr', '( %s -> I = J )' % p11)
    g1 = s([s([ij], 'fveq2d', '( %s -> ( %s ` I ) = ( %s ` J ) )' % (p11, UPDT, UPDT))], 'id', '') if False else \
        s([ij], 'fveq2d', '( %s -> ( %s ` I ) = ( %s ` J ) )' % (p11, UPDT, UPDT))
    jv = s([L(p11, jn, p1) if False else s([L(p1, jn)], 'adantr', '( %s -> J e. NN0 )' % p11)], 'elexd', '( %s -> J e. _V )' % p11)
    iv = s([s([], 'fvex', '( inl ` W ) e. _V')], 'a1i', '( %s -> ( inl ` W ) e. _V )' % p11)
    dm = s([s([], 'resdmss', 'dom ( A |` ( NN0 \\ { J } ) ) C_ ( NN0 \\ { J } )')], 'a1i', '( %s -> dom ( A |` ( NN0 \\ { J } ) ) C_ ( NN0 \\ { J } ) )' % p11)
    nd = s([s([], 'neldifsn', '-. J e. ( NN0 \\ { J } )')], 'a1i', '( %s -> -. J e. ( NN0 \\ { J } ) )' % p11)
    nj = s([dm, nd], 'ssneldd', '( %s -> -. J e. dom ( A |` ( NN0 \\ { J } ) ) )' % p11)
    g2 = s([jv, iv, nj, w.inst('fsnunfv')], 'syl3anc', '( %s -> ( %s ` J ) = ( inl ` W ) )' % (p11, UPDT))
    lhs = s([s([L(p11, f1, p1), g1], 'eqtrd', '( %s -> ( %s ` I ) = ( %s ` J ) )' % (p11, AP, UPDT)), g2], 'eqtrd',
            '( %s -> ( %s ` I ) = ( inl ` W ) )' % (p11, AP))
    r1 = s([ij], 'iftrued', '( %s -> %s = %s )' % (p11, RHS, FILLA))
    r2 = s([L(p11, c1, p1)], 'iftrued', '( %s -> %s = ( inl ` W ) )' % (p11, FILLA))
    rr = s([r1, r2], 'eqtrd', '( %s -> %s = ( inl ` W ) )' % (p11, RHS))
    o11 = s([lhs, rr], 'eqtr4d', GOAL(p11))
    #   I =/= J
    p12 = '( %s /\\ -. I = J )' % p1
    nij = s([], 'simpr', '( %s -> -. I = J )' % p12)
    ine = s([nij], 'neqned', '( %s -> I =/= J )' % p12)
    jne = s([ine], 'necomd', '( %s -> J =/= I )' % p12)
    u1 = s([jne, w.inst('fvunsn')], 'syl', '( %s -> ( %s ` I ) = ( ( A |` ( NN0 \\ { J } ) ) ` I ) )' % (p12, UPDT))
    ind = s([s([s([L(p1, inn)], 'adantr', '( %s -> I e. NN0 )' % p12), ine], 'jca', '( %s -> ( I e. NN0 /\\ I =/= J ) )' % p12), w.inst('eldifsn')],
            'sylibr', '( %s -> I e. ( NN0 \\ { J } ) )' % p12)
    u2 = s([ind, w.inst('fvres')], 'syl', '( %s -> ( ( A |` ( NN0 \\ { J } ) ) ` I ) = ( A ` I ) )' % p12)
    lhs2 = s([s([L(p12, f1, p1), u1], 'eqtrd', '( %s -> ( %s ` I ) = ( ( A |` ( NN0 \\ { J } ) ) ` I ) )' % (p12, AP)), u2], 'eqtrd',
             '( %s -> ( %s ` I ) = ( A ` I ) )' % (p12, AP))
    rr2 = s([nij], 'iffalsed', '( %s -> %s = ( A ` I ) )' % (p12, RHS))
    o12 = s([lhs2, rr2], 'eqtr4d', GOAL(p12))
    o1 = s([o11, o12], 'pm2.61dan', GOAL(p1))
    # case A ` J =/= none
    p2 = '( %s /\\ -. %s )' % (ph, C1)
    c2 = s([], 'simpr', '( %s -> -. %s )' % (p2, C1))
    e2 = s([L(p2, sv), s([c2], 'iffalsed', '( %s -> if ( %s , %s , A ) = A )' % (p2, C1, UPDT))], 'eqtrd', '( %s -> %s = A )' % (p2, AP))
    f2 = s([e2], 'fveq1d', '( %s -> ( %s ` I ) = ( A ` I ) )' % (p2, AP))
    p21 = '( %s /\\ I = J )' % p2
    ij2 = s([], 'simpr', '( %s -> I = J )' % p21)
    q1 = s([ij2], 'iftrued', '( %s -> %s = %s )' % (p21, RHS, FILLA))
    q2 = s([L(p21, c2, p2)], 'iffalsed', '( %s -> %s = ( A ` J ) )' % (p21, FILLA))
    q3 = s([ij2], 'fveq2d', '( %s -> ( A ` I ) = ( A ` J ) )' % p21)
    rq = s([s([q1, q2], 'eqtrd', '( %s -> %s = ( A ` J ) )' % (p21, RHS)), q3], 'eqtr4d', '( %s -> %s = ( A ` I ) )' % (p21, RHS))
    o21 = s([L(p21, f2, p2), rq], 'eqtr4d', GOAL(p21))
    p22 = '( %s /\\ -. I = J )' % p2
    rq2 = s([s([], 'simpr', '( %s -> -. I = J )' % p22)], 'iffalsed', '( %s -> %s = ( A ` I ) )' % (p22, RHS))
    o22 = s([L(p22, f2, p2), rq2], 'eqtr4d', GOAL(p22))
    o2 = s([o21, o22], 'pm2.61dan', GOAL(p2))
    w.qed([o1, o2], 'pm2.61dan', ST_FV)
    return w.run()


def ttwsplit():
    ph = '( V e. Word S /\\ J e. ( 0 ..^ ( # ` V ) ) )'
    w = W('ttwsplit', 'A word is its prefix up to ` J ` , its letter at ` J ` and its rest after ` J ` (Lean '
                      '` List.take_append_drop ` , ` List.drop_eq_getElem_cons ` ).')
    s = w.s
    vw = s([], 'simpl', '( %s -> V e. Word S )' % ph)
    jo = s([], 'simpr', '( %s -> J e. ( 0 ..^ ( # ` V ) ) )' % ph)
    NV = '( # ` V )'
    jfz = s([jo, w.inst('elfzofz')], 'syl', '( %s -> J e. ( 0 ... %s ) )' % (ph, NV))
    j1 = s([jo, w.inst('fzofzp1')], 'syl', '( %s -> ( J + 1 ) e. ( 0 ... %s ) )' % (ph, NV))
    jn = s([jo, w.inst('elfzonn0')], 'syl', '( %s -> J e. NN0 )' % ph)
    jj = s([s([jn, w.inst('fzonn0p1')], 'syl', '( %s -> J e. ( 0 ..^ ( J + 1 ) ) )' % ph), w.inst('elfzofz')], 'syl',
           '( %s -> J e. ( 0 ... ( J + 1 ) ) )' % ph)
    nv = s([vw, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, NV))
    nn = s([nv, w.inst('nn0fz0')], 'sylib', '( %s -> %s e. ( 0 ... %s ) )' % (ph, NV, NV))
    cs = s([vw, s([jj, j1, nn], '3jca', '( %s -> ( J e. ( 0 ... ( J + 1 ) ) /\\ ( J + 1 ) e. ( 0 ... %s ) /\\ %s e. ( 0 ... %s ) ) )' % (ph, NV, NV, NV)),
            w.inst('ccatswrd')], 'syl2anc',
           '( %s -> ( ( V substr <. J , ( J + 1 ) >. ) ++ ( V substr <. ( J + 1 ) , %s >. ) ) = ( V substr <. J , %s >. ) )' % (ph, NV, NV))
    s1 = s([vw, jo, w.inst('swrds1')], 'syl2anc', '( %s -> ( V substr <. J , ( J + 1 ) >. ) = <" ( V ` J ) "> )' % ph)
    REST = '( V substr <. ( J + 1 ) , %s >. )' % NV
    a = s([s([s1], 'oveq1d', '( %s -> ( ( V substr <. J , ( J + 1 ) >. ) ++ %s ) = ( <" ( V ` J ) "> ++ %s ) )' % (ph, REST, REST)), cs], 'eqtr3d',
          '( %s -> ( <" ( V ` J ) "> ++ %s ) = ( V substr <. J , %s >. ) )' % (ph, REST, NV))
    pc = s([vw, jfz, w.inst('pfxcctswrd')], 'syl2anc', '( %s -> ( ( V prefix J ) ++ ( V substr <. J , %s >. ) ) = V )' % (ph, NV))
    b = s([a], 'oveq2d', '( %s -> ( ( V prefix J ) ++ ( <" ( V ` J ) "> ++ %s ) ) = ( ( V prefix J ) ++ ( V substr <. J , %s >. ) ) )' % (ph, REST, NV))
    e = s([b, pc], 'eqtrd', '( %s -> ( ( V prefix J ) ++ ( <" ( V ` J ) "> ++ %s ) ) = V )' % (ph, REST))
    w.qed([e], 'eqcomd', ST_SPL)
    return w.run()


def ttsetsl():
    ph = PH_SL
    w = W('ttsetsl', 'The first ` L ` slots of the guarded write ( ` J < L ` ) are the first ` L ` slots of the table with '
                     'slot ` J ` filled: Lean\'s ` map_range_setIfNone ` with ` setSlotL_eq_take_cons_drop ` .')
    s = w.s
    c = Ctx(w, ph, parse_conj(ph))
    at, ln, jn, jlt, ww = c['A e. Tbl'], c['L e. NN0'], c['J e. NN0'], c['J < L'], c['W e. Word NN0']
    apt = s([s([at, jn], 'jca', '( %s -> ( A e. Tbl /\\ J e. NN0 ) )' % ph), ww, w.inst('setifnonecl')], 'syl2anc', '( %s -> %s e. Tbl )' % (ph, AP))
    def tw(T):
        t = s([s([T[1], ln], 'jca', '( %s -> ( %s e. Tbl /\\ L e. NN0 ) )' % (ph, T[0])), w.inst('tttblw')], 'syl',
              '( %s -> ( ( %s |` ( 0 ..^ L ) ) e. %s /\\ ( # ` ( %s |` ( 0 ..^ L ) ) ) = L ) )' % (ph, T[0], WSLOT, T[0]))
        return (s([t], 'simpld', '( %s -> ( %s |` ( 0 ..^ L ) ) e. %s )' % (ph, T[0], WSLOT)),
                s([t], 'simprd', '( %s -> ( # ` ( %s |` ( 0 ..^ L ) ) ) = L )' % (ph, T[0])))
    wpw, wpl = tw((AP, apt))
    wlw, wll = tw(('A', at))
    lz = s([ln], 'nn0zd', '( %s -> L e. ZZ )' % ph)
    jo = s([s([jn, lz, jlt], '3jca', '( %s -> ( J e. NN0 /\\ L e. ZZ /\\ J < L ) )' % ph), w.inst('elfzo0z')], 'sylibr', '( %s -> J e. ( 0 ..^ L ) )' % ph)
    jop = s([jo, s([wpl], 'oveq2d', '( %s -> ( 0 ..^ ( # ` %s ) ) = ( 0 ..^ L ) )' % (ph, WLP))], 'eleqtrrd', '( %s -> J e. ( 0 ..^ ( # ` %s ) ) )' % (ph, WLP))
    spl = s([wpw, jop, w.inst('ttwsplit')], 'syl2anc',
            '( %s -> %s = ( ( %s prefix J ) ++ ( <" ( %s ` J ) "> ++ ( %s substr <. ( J + 1 ) , ( # ` %s ) >. ) ) ) )' % (ph, WLP, WLP, WLP, WLP, WLP))
    # values
    def fvv(p, X, xo):
        """( p -> ( WLP ` X ) = if ( X = J , FILLA , ( A ` X ) ) ) and ( p -> ( WL ` X ) = ( A ` X ) ) from xo : X e. ( 0 ..^ L )"""
        L_ = lambda st: s([st], 'adantr', '( %s -> %s )' % (p, concl(w, ph, st))) if p != ph else st
        r1 = s([xo, w.inst('fvres')], 'syl', '( %s -> ( %s ` %s ) = ( %s ` %s ) )' % (p, WLP, X, AP, X))
        xn = s([xo, w.inst('elfzonn0')], 'syl', '( %s -> %s e. NN0 )' % (p, X))
        tfv = tsub_text(ST_FV, {'I': X})
        a3 = s([L_(at), L_(jn), L_(ww)], '3jca', '( %s -> ( A e. Tbl /\\ J e. NN0 /\\ W e. Word NN0 ) )' % p)
        r2 = s([a3, xn, w.inst('ttsetfv')], 'syl2anc', '( %s -> ( %s ` %s ) = if ( %s = J , %s , ( A ` %s ) ) )' % (p, AP, X, X, FILLA, X))
        r3 = s([xo, w.inst('fvres')], 'syl', '( %s -> ( %s ` %s ) = ( A ` %s ) )' % (p, WL, X, X))
        return s([r1, r2], 'eqtrd', '( %s -> ( %s ` %s ) = if ( %s = J , %s , ( A ` %s ) ) )' % (p, WLP, X, X, FILLA, X)), r3
    # the prefix
    p1 = '( %s /\\ i e. ( 0 ..^ J ) )' % ph
    Lp = lambda st: s([st], 'adantr', '( %s -> %s )' % (p1, concl(w, ph, st)))
    io = s([], 'simpr', '( %s -> i e. ( 0 ..^ J ) )' % p1)
    jl = s([Lp(jn), Lp(ln), Lp(jlt)], 'id', '') if False else None
    jle = s([s([Lp(jn)], 'nn0red', '( %s -> J e. RR )' % p1), s([Lp(ln)], 'nn0red', '( %s -> L e. RR )' % p1), Lp(jlt)], 'ltled', '( %s -> J <_ L )' % p1)
    ss = s([s([Lp(lz), jle], 'jca', '( %s -> ( L e. ZZ /\\ J <_ L ) )' % p1) if False else jle, w.inst('fzoss2')], 'syl' if False else 'id', '') if False else None
    luz = s([s([Lp(jn)], 'nn0zd', '( %s -> J e. ZZ )' % p1), Lp(lz), jle], 'eluz2' if False else 'id', '') if False else None
    luz = s([s([s([Lp(jn)], 'nn0zd', '( %s -> J e. ZZ )' % p1), Lp(lz), jle], '3jca', '( %s -> ( J e. ZZ /\\ L e. ZZ /\\ J <_ L ) )' % p1), w.inst('eluz2')],
            'sylibr', '( %s -> L e. ( ZZ>= ` J ) )' % p1)
    fs = s([luz, w.inst('fzoss2')], 'syl', '( %s -> ( 0 ..^ J ) C_ ( 0 ..^ L ) )' % p1)
    iol = s([fs, io], 'sseldd', '( %s -> i e. ( 0 ..^ L ) )' % p1)
    v1, v2 = fvv(p1, 'i', iol)
    ilt = s([io, w.inst('elfzolt2')], 'syl', '( %s -> i < J )' % p1)
    ine = s([s([s([s([io, w.inst('elfzonn0')], 'syl', '( %s -> i e. NN0 )' % p1)], 'nn0red', '( %s -> i e. RR )' % p1), ilt], 'ltned', '( %s -> i =/= J )' % p1)],
            'neneqd', '( %s -> -. i = J )' % p1)
    v3 = s([v1, s([ine], 'iffalsed', '( %s -> if ( i = J , %s , ( A ` i ) ) = ( A ` i ) )' % (p1, FILLA))], 'eqtrd', '( %s -> ( %s ` i ) = ( A ` i ) )' % (p1, WLP))
    pe1 = s([v3, v2], 'eqtr4d', '( %s -> ( %s ` i ) = ( %s ` i ) )' % (p1, WLP, WL))
    ra1 = s([pe1], 'ralrimiva', '( %s -> A. i e. ( 0 ..^ J ) ( %s ` i ) = ( %s ` i ) )' % (ph, WLP, WL))
    jle0 = s([s([jn], 'nn0red', '( %s -> J e. RR )' % ph), s([ln], 'nn0red', '( %s -> L e. RR )' % ph), jlt], 'ltled', '( %s -> J <_ L )' % ph)
    j1 = s([jle0, s([wpl], 'eqcomd', '( %s -> L = ( # ` %s ) )' % (ph, WLP))], 'breqtrd', '( %s -> J <_ ( # ` %s ) )' % (ph, WLP))
    j2 = s([jle0, s([wll], 'eqcomd', '( %s -> L = ( # ` %s ) )' % (ph, WL))], 'breqtrd', '( %s -> J <_ ( # ` %s ) )' % (ph, WL))
    pq = s([s([wpw, wlw], 'jca', '( %s -> ( %s e. %s /\\ %s e. %s ) )' % (ph, WLP, WSLOT, WL, WSLOT)), s([jn, jn], 'jca', '( %s -> ( J e. NN0 /\\ J e. NN0 ) )' % ph),
            s([j1, j2], 'jca', '( %s -> ( J <_ ( # ` %s ) /\\ J <_ ( # ` %s ) ) )' % (ph, WLP, WL)), w.inst('pfxeq')], 'syl3anc',
           '( %s -> ( ( %s prefix J ) = ( %s prefix J ) <-> ( J = J /\\ A. i e. ( 0 ..^ J ) ( %s ` i ) = ( %s ` i ) ) ) )' % (ph, WLP, WL, WLP, WL))
    jj = s([], 'eqidd', '( %s -> J = J )' % ph)
    pfe = s([s([jj, ra1], 'jca', '( %s -> ( J = J /\\ A. i e. ( 0 ..^ J ) ( %s ` i ) = ( %s ` i ) ) )' % (ph, WLP, WL)), pq], 'mpbird',
            '( %s -> ( %s prefix J ) = ( %s prefix J ) )' % (ph, WLP, WL))
    # the rest
    J1 = '( J + 1 )'
    p2 = '( %s /\\ i e. ( %s ..^ L ) )' % (ph, J1)
    Lq = lambda st: s([st], 'adantr', '( %s -> %s )' % (p2, concl(w, ph, st)))
    io2 = s([], 'simpr', '( %s -> i e. ( %s ..^ L ) )' % (p2, J1))
    j1n = s([Lq(jn), w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (p2, J1))
    fs2 = s([j1n, w.inst('fzoss1')], 'syl' if False else 'id', '') if False else None
    j1z = s([j1n], 'nn0zd', '( %s -> %s e. ZZ )' % (p2, J1))
    u0 = s([j1n, w.inst('nn0uz' if False else 'id')], 'id', '') if False else None
    j0 = s([s([j1n, w.inst('elnn0uz')], 'sylib', '( %s -> %s e. ( ZZ>= ` 0 ) )' % (p2, J1)), w.inst('fzoss1')], 'syl',
           '( %s -> ( %s ..^ L ) C_ ( 0 ..^ L ) )' % (p2, J1))
    iol2 = s([j0, io2], 'sseldd', '( %s -> i e. ( 0 ..^ L ) )' % p2)
    w1, w2 = fvv(p2, 'i', iol2)
    ige = s([io2, w.inst('elfzole1')], 'syl', '( %s -> %s <_ i )' % (p2, J1))
    jr = s([Lq(jn)], 'nn0red', '( %s -> J e. RR )' % p2)
    ir = s([s([iol2, w.inst('elfzonn0')], 'syl', '( %s -> i e. NN0 )' % p2)], 'nn0red', '( %s -> i e. RR )' % p2)
    cl2 = Closure(w, p2, {'J': ('RR', jr), 'i': ('RR', ir)})
    jli = linarith(w, p2, [ige], 'J < i', closure=cl2)
    ine2 = s([s([s([jr, jli], 'ltned', '( %s -> J =/= i )' % p2)], 'necomd', '( %s -> i =/= J )' % p2)], 'neneqd', '( %s -> -. i = J )' % p2)
    w3 = s([w1, s([ine2], 'iffalsed', '( %s -> if ( i = J , %s , ( A ` i ) ) = ( A ` i ) )' % (p2, FILLA))], 'eqtrd', '( %s -> ( %s ` i ) = ( A ` i ) )' % (p2, WLP))
    pe2 = s([w3, w2], 'eqtr4d', '( %s -> ( %s ` i ) = ( %s ` i ) )' % (p2, WLP, WL))
    ra2 = s([pe2], 'ralrimiva', '( %s -> A. i e. ( %s ..^ L ) ( %s ` i ) = ( %s ` i ) )' % (ph, J1, WLP, WL))
    j1n0 = s([jn, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (ph, J1))
    lr = s([s([ln], 'nn0red', '( %s -> L e. RR )' % ph)], 'leidd', '( %s -> L <_ L )' % ph)
    l1 = s([lr, s([wpl], 'eqcomd', '( %s -> L = ( # ` %s ) )' % (ph, WLP))], 'breqtrd', '( %s -> L <_ ( # ` %s ) )' % (ph, WLP))
    l2 = s([lr, s([wll], 'eqcomd', '( %s -> L = ( # ` %s ) )' % (ph, WL))], 'breqtrd', '( %s -> L <_ ( # ` %s ) )' % (ph, WL))
    sq = s([s([wpw, wlw], 'jca', '( %s -> ( %s e. %s /\\ %s e. %s ) )' % (ph, WLP, WSLOT, WL, WSLOT)), s([j1n0, ln], 'jca', '( %s -> ( %s e. NN0 /\\ L e. NN0 ) )' % (ph, J1)),
            s([l1, l2], 'jca', '( %s -> ( L <_ ( # ` %s ) /\\ L <_ ( # ` %s ) ) )' % (ph, WLP, WL)), w.inst('swrdspsleq')], 'syl3anc',
           '( %s -> ( ( %s substr <. %s , L >. ) = ( %s substr <. %s , L >. ) <-> A. i e. ( %s ..^ L ) ( %s ` i ) = ( %s ` i ) ) )' % (ph, WLP, J1, WL, J1, J1, WLP, WL))
    dre = s([ra2, sq], 'mpbird', '( %s -> ( %s substr <. %s , L >. ) = ( %s substr <. %s , L >. ) )' % (ph, WLP, J1, WL, J1))
    # the letter at J
    x1, x2 = fvv(ph, 'J', jo)
    x3 = s([x1, s([s([], 'eqidd', '( %s -> J = J )' % ph)], 'iftrued', '( %s -> if ( J = J , %s , ( A ` J ) ) = %s )' % (ph, FILLA, FILLA))], 'eqtrd',
           '( %s -> ( %s ` J ) = %s )' % (ph, WLP, FILLA))
    fr, fnew = w.rewrite(FILLW, {'( %s ` J )' % WL: ('( A ` J )', x2)}, ph)
    assert fnew == FILLA, fnew
    x4 = s([x3, fr], 'eqtr4d', '( %s -> ( %s ` J ) = %s )' % (ph, WLP, FILLW))
    # assemble
    rules = {'( %s prefix J )' % WLP: ('( %s prefix J )' % WL, pfe), '( %s ` J )' % WLP: (FILLW, x4),
             '( # ` %s )' % WLP: ('L', wpl)}
    r1, n1 = w.rewrite(concl(w, ph, spl).split(' = ', 1)[1], rules, ph)
    exp1 = '( ( %s prefix J ) ++ ( <" %s "> ++ ( %s substr <. %s , L >. ) ) )' % (WL, FILLW, WLP, J1)
    assert n1 == exp1, n1
    r2, n2 = w.rewrite(n1, {'( %s substr <. %s , L >. )' % (WLP, J1): ('( %s substr <. %s , L >. )' % (WL, J1), dre)}, ph)
    r3, n3 = w.rewrite(SSLJ, {'( # ` %s )' % WL: ('L', wll)}, ph)
    assert n3 == n2, (n3, n2)
    fin = s([s([s([spl, r1], 'eqtrd', '( %s -> %s = %s )' % (ph, WLP, n1)), r2], 'eqtrd', '( %s -> %s = %s )' % (ph, WLP, n2)), r3], 'eqtr4d',
            '( %s -> %s = %s )' % (ph, WLP, SSLJ))
    w.lines[-1] = 'qed:' + w.lines[-1].split(':', 1)[1]
    return w.run()


def tmisint():
    lab = 'tmisint'
    ph = cj(TREE_SINT)
    w = W(lab, 'Lean\'s ` setIfNoneF_tbl ` at the machine: wherever ` setIfNoneF tbl j w s scr ` is installed, the '
               'table ` A ` on ` tbl ` (bounded by ` TblBounded ` ) becomes ` Alg.setIfNone A jn W ` , within '
               '` setC jn N b m ` steps (~ tmisin on the slot word, ~ ttsetsl ).')
    c = Ctx(w, ph, TREE_SINT)
    s = w.s
    t = tbl_prep(w, ph, c)
    WLt = '( A |` ( 0 ..^ L ) )'
    dk = s([c['( D ` K ) = ( ( L encTblAsc A ) ++ X )'], s([t['ea']], 'oveq1d', '( %s -> ( ( L encTblAsc A ) ++ X ) = ( %s ++ X ) )' % (ph, ES(WLt)))],
           'eqtrd', '( %s -> ( D ` K ) = ( %s ++ X ) )' % (ph, ES(WLt)))
    jl = s([c['%s < L' % JN], t['wl']], 'breqtrrd', '( %s -> %s < ( # ` %s ) )' % (ph, JN, WLt))
    ex = {'%s e. %s' % (WLt, WSLOT): t['ww'], '( D ` K ) = ( %s ++ X )' % ES(WLt): dk, '%s < ( # ` %s )' % (JN, WLt): jl,
          'A. o e. ran %s %s' % (WLt, SB('o')): t['sb']}
    t1, cc = inst(w, ph, 'tmisin', {'L': WLt}, Bld(w, ph, c, ex))
    C1, D1, n1 = triple_parts(cc)
    jnn = s([c['G e. Word 2o'], w.inst('tonatcl')], 'syl', '( %s -> %s e. NN0 )' % (ph, JN))
    APJ = tsub_text(AP, {'J': JN})
    sl = s([s([s([t['at'], t['ln']], 'jca', '( %s -> ( A e. Tbl /\\ L e. NN0 ) )' % ph),
               s([jnn, c['%s < L' % JN], c['W e. Word NN0']], '3jca', '( %s -> ( %s e. NN0 /\\ %s < L /\\ W e. Word NN0 ) )' % (ph, JN, JN))], 'jca',
              '( %s -> %s )' % (ph, tsub_text(PH_SL, {'J': JN}))), w.inst('ttsetsl')], 'syl', '( %s -> %s )' % (ph, tsub_text(ST_SL, {'J': JN}).split(' -> ', 1)[1][:-2]))
    apt = s([s([t['at'], jnn], 'jca', '( %s -> ( A e. Tbl /\\ %s e. NN0 ) )' % (ph, JN)), c['W e. Word NN0'], w.inst('setifnonecl')], 'syl2anc',
            '( %s -> %s e. Tbl )' % (ph, APJ))
    te = s([s([apt, t['ln']], 'jca', '( %s -> ( %s e. Tbl /\\ L e. NN0 ) )' % (ph, APJ)), w.inst('tttbles')], 'syl',
           '( %s -> ( ( L encTblAsc %s ) = %s /\\ ( L encTblDesc %s ) = %s ) )' % (ph, APJ, ES('( %s |` ( 0 ..^ L ) )' % APJ), APJ,
                                                                                 ES(REV('( %s |` ( 0 ..^ L ) )' % APJ))))
    ea = s([te], 'simpld', '( %s -> ( L encTblAsc %s ) = %s )' % (ph, APJ, ES('( %s |` ( 0 ..^ L ) )' % APJ)))
    SSLW = tsub_text(SSL, {'L': WLt})
    e1 = s([s([sl], 'fveq2d', '( %s -> %s = %s )' % (ph, ES('( %s |` ( 0 ..^ L ) )' % APJ), ES(SSLW)))], 'id', '') if False else \
        s([sl], 'fveq2d', '( %s -> %s = %s )' % (ph, ES('( %s |` ( 0 ..^ L ) )' % APJ), ES(SSLW)))
    e2 = s([e1, ea], 'eqtr2d' if False else 'eqtr3d', '( %s -> %s = ( L encTblAsc %s ) )' % (ph, ES(SSLW), APJ)) if False else \
        s([ea, e1], 'eqtr2d', '( %s -> %s = ( L encTblAsc %s ) )' % (ph, ES(SSLW), APJ))
    r, new = w.rewrite(D1, {ES(SSLW): ('( L encTblAsc %s )' % APJ, e2)}, ph)
    assert new == CE(DFIN_SINT), new
    hrrw(w, ph, t1, C1, D1, n1, deq=r, qed=True)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
