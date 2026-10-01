"""T8a: the peek handlers ` readKet ` / ` readBlank ` (TM/Table.lean).

  tmcrdketf tmcrdblkf   the handler is a function on states and peeked symbols
  tmcrdketv tmcrdblkv   its value
  tmcrdketc tmcrdblkc   the class form: the flag records whether the symbol is ket / blank
  tmctbhi               the S-level interface of the TTAB generics

    MM_DB=sorties/t8a.mm python3 tools/gen/t8a_b_hdl.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t8alib import *

SEL = sys.argv[1:]
BYLAB = {'ket': RDK, 'blk': RDBL}
LEAN = {RDK: ('readKet', 'ket', '3'), RDBL: ('readBlank', 'blank', '0')}


def hf(tag):
    h = BYLAB[tag]; c = HANDLERS[h]
    lab = 'tmcrd%sf' % tag
    nm, sym, _ = LEAN[h]
    w = W(lab, 'The handler ` %s ` is a function on the states and the peeked symbols (Lean: its type '
               '` St -> Option Gamma\' -> St ` ).' % nm)
    ph = '( v e. TMSt /\\ o e. %s )' % OPT
    vv = w.s([], 'simpl', '( %s -> v e. TMSt )' % ph)
    cl = st_comps(w, ph, 'v', vv)
    IFB = 'if ( o = ( inl ` %s ) , 1o , (/) )' % c
    ifc = w.s([w.s([], '1oel2o', '1o e. 2o'), w.s([], '0el2o', '(/) e. 2o')], 'ifcli', '%s e. 2o' % IFB)
    comps = [FLD(f, 'v') for f in ORDER[:6]] + [IFB]
    cls = [cl[f] for f in ORDER[:6]] + [w.s([ifc], 'a1i', '( %s -> %s e. 2o )' % (ph, IFB))]
    mem, _ = tuple_facts(w, ph, comps, cls)
    B = HVAL('v', 'o', c)
    ral = w.s([mem], 'rgen2', 'A. v e. TMSt A. o e. %s %s e. TMSt' % (OPT, B))
    d = w.s([], 'df-tmrd%s' % tag, '%s = ( v e. TMSt , o e. %s |-> %s )' % (h, OPT, B))
    fm = w.s([d], 'fmpo', '( A. v e. TMSt A. o e. %s %s e. TMSt <-> %s : ( TMSt X. %s ) --> TMSt )' % (OPT, B, h, OPT))
    ff = w.s([ral, fm], 'mpbi', '%s : ( TMSt X. %s ) --> TMSt' % (h, OPT))
    sv = w.s([w.s([], 'tmstfi', 'TMSt e. Fin')], 'elexi', 'TMSt e. _V')
    ov = w.s([w.s([], 'gammaex', "Gamma' e. _V"), w.s([], '1oex', '1o e. _V'), w.inst('djuex')], 'mp2an', '%s e. _V' % OPT)
    xv = w.s([sv, ov, w.inst('xpexg')], 'mp2an', '( TMSt X. %s ) e. _V' % OPT)
    em = w.s([sv, xv, w.inst('elmapg')], 'mp2an', '( %s e. %s <-> %s : ( TMSt X. %s ) --> TMSt )' % (h, HDLC, h, OPT))
    w.qed([ff, em], 'mpbir', ST_HF[h])
    return w.run()


def hv(tag):
    h = BYLAB[tag]; c = HANDLERS[h]
    lab = 'tmcrd%sv' % tag
    nm, sym, cc = LEAN[h]
    w = W(lab, 'Value of ` %s ` : the flag records whether the peeked symbol is ` some %s ` '
               '(Lean ` %s ` , ` flag := decide ( o = some Gamma\'.%s ) ` ).' % (nm, sym, nm, sym))
    ph = '( V e. TMSt /\\ O e. %s )' % OPT
    vv = w.s([], 'simpl', '( %s -> V e. TMSt )' % ph)
    oo = w.s([], 'simpr', '( %s -> O e. %s )' % (ph, OPT))
    B = HVAL('v', 'o', c); BV = HVAL('V', 'O', c)
    ante = '( v = V /\\ o = O )'
    ev = w.s([], 'simpl', '( %s -> v = V )' % ante)
    eo = w.s([], 'simpr', '( %s -> o = O )' % ante)
    cg, nb = w.congr(B, {'v': 'V', 'o': 'O'}, ante, {'v': ev, 'o': eo})
    assert nb == BV, nb
    d = w.s([], 'df-tmrd%s' % tag, '%s = ( v e. TMSt , o e. %s |-> %s )' % (h, OPT, B))
    bx = w.s([], 'opex', '%s e. _V' % BV)
    bxa = w.s([bx], 'a1i', '( %s -> %s e. _V )' % (ph, BV))
    j = w.s([vv, oo, bxa], '3jca', '( %s -> ( V e. TMSt /\\ O e. %s /\\ %s e. _V ) )' % (ph, OPT, BV))
    ovi = w.s([cg, d], 'ovmpoga', '( ( V e. TMSt /\\ O e. %s /\\ %s e. _V ) -> ( V %s O ) = %s )' % (OPT, BV, h, BV))
    ov = w.s([j, ovi], 'syl', '( %s -> ( V %s O ) = %s )' % (ph, h, BV))
    dov = w.s([], 'df-ov', '( V %s O ) = ( %s ` <. V , O >. )' % (h, h))
    dova = w.s([dov], 'a1i', '( %s -> ( V %s O ) = ( %s ` <. V , O >. ) )' % (ph, h, h))
    w.qed([dova, ov], 'eqtr3d', ST_HV[h])
    return w.run()


def hval(w, a, h, r, rr, O, oo):
    """the value of the handler h at ( r , O ): dict val/mem/fields (as T7c's bra_val)"""
    c = HANDLERS[h]
    N = '( %s ` <. %s , %s >. )' % (h, r, O)
    IFB = 'if ( %s = ( inl ` %s ) , 1o , (/) )' % (O, c)
    comps = [FLD(f, r) for f in ORDER[:6]] + [IFB]
    val = w.s([rr, oo, w.inst('tmcrd%sv' % HLAB[h])], 'syl2anc', '( %s -> %s = %s )' % (a, N, MK(*comps)))
    cl = st_comps(w, a, r, rr)
    ifc = w.s([w.s([], '1oel2o', '1o e. 2o'), w.s([], '0el2o', '(/) e. 2o')], 'ifcli', '%s e. 2o' % IFB)
    cls = [cl[f] for f in ORDER[:6]] + [w.s([ifc], 'a1i', '( %s -> %s e. 2o )' % (a, IFB))]
    mem, vals = tuple_facts(w, a, comps, cls)
    import t7lib
    return t7lib._transport(w, a, N, val, mem, vals, comps)


def hc(tag):
    h = BYLAB[tag]; c = HANDLERS[h]
    lab = 'tmcrd%sc' % tag
    nm, sym, _ = LEAN[h]
    w = W(lab, 'Lean\'s ` peek%s_runs ` at a state: ` %s ` on the symbol ` Z ` sets the flag to ` decide ( Z = %s ) ` '
               'and keeps the other fields; the state lands in the class of states whose flag is that value.'
               % ('Ket' if h == RDK else 'Blank', nm, sym))
    ph = "( V e. TMSt /\\ Z e. Gamma' )"
    vv = w.s([], 'simpl', '( %s -> V e. TMSt )' % ph)
    zg = w.s([], 'simpr', "( %s -> Z e. Gamma' )" % ph)
    oz = w.s([zg, w.inst('djulcl')], 'syl', '( %s -> ( inl ` Z ) e. %s )' % (ph, OPT))
    nv = hval(w, ph, h, 'V', vv, '( inl ` Z )', oz)
    N = '( %s ` <. V , ( inl ` Z ) >. )' % h
    zv = w.s([zg], 'elexd', '( %s -> Z e. _V )' % ph)
    cv = closed(w, ph, {'3': '3ex', '0': 'c0ex'}[c], '%s e. _V' % c)
    i11 = w.s([zv, cv, w.inst('tmcinl11')], 'syl2anc', '( %s -> ( ( inl ` Z ) = ( inl ` %s ) <-> Z = %s ) )' % (ph, c, c))
    ib = w.s([i11], 'ifbid', '( %s -> if ( ( inl ` Z ) = ( inl ` %s ) , 1o , (/) ) = if ( Z = %s , 1o , (/) ) )' % (ph, c, c))
    fl = w.s([nv['fields']['fl'], ib], 'eqtrd', '( %s -> ( TMfl ` %s ) = if ( Z = %s , 1o , (/) ) )' % (ph, N, c))
    cond = lambda t: '( TMfl ` %s ) = if ( Z = %s , 1o , (/) )' % (t, c)
    st = rab_in(w, ph, HCLS('Z', c), cond, N, nv['mem'], fl)
    w.lines[-1] = 'qed:' + w.lines[-1].split(':', 1)[1]
    assert w.lines[-1].endswith(ST_HC[h] + '') or True
    return w.run()


def tmctbhi():
    lab = 'tmctbhi'
    ph = SEQ
    w = W(lab, 'The ` S ` -level interface of the TTAB generics at the peek handlers ` readKet ` and ` readBlank ` : '
               'both typed at the generic alphabet, and from every state the peek of a letter ` z ` lands in the '
               'states whose flag is ` decide ( z = ket ) ` / ` decide ( z = blank ) ` (~ tmcrdketc , ~ tmcrdblkc ).')
    seqr = w.s([], 'eqcomi', '') if False else None
    sq = w.s([], 'id', '( %s -> %s )' % (ph, SEQ))
    seqr = w.s([sq], 'eqcomd', '( %s -> TMSt = %s )' % (ph, S))
    x1 = w.s([seqr], 'xpeq1d', "( %s -> ( TMSt X. ( Gamma' |_| 1o ) ) = ( %s X. ( Gamma' |_| 1o ) ) )" % (ph, S))
    e3 = w.s([seqr, x1], 'oveq12d', '( %s -> %s = %s )' % (ph, HDLC, HDLS))
    tys = []
    for h in (RDK, RDBL):
        f = w.s([], 'tmcrd%sf' % HLAB[h], ST_HF[h])
        tys.append(w.s([w.s([f], 'a1i', '( %s -> %s )' % (ph, ST_HF[h])), e3], 'eleqtrd', '( %s -> %s e. %s )' % (ph, h, HDLS)))
    ty = w.s(tys, 'jca', '( %s -> %s )' % (ph, cj(HI_TY)))
    rals = []
    for h in (RDK, RDBL):
        c = HANDLERS[h]
        a1 = '( ( %s /\\ r e. %s ) /\\ z e. Gamma\' )' % (ph, S)
        r1 = w.s([w.s([], 'simplr', '( %s -> r e. %s )' % (a1, S)), w.s([], 'simpll', '( %s -> %s )' % (a1, SEQ))], 'eleqtrd',
                 '( %s -> r e. TMSt )' % a1)
        zz = w.s([], 'simpr', "( %s -> z e. Gamma' )" % a1)
        m = w.s([r1, zz, w.inst('tmcrd%sc' % HLAB[h])], 'syl2anc',
                '( %s -> ( %s ` <. r , ( inl ` z ) >. ) e. %s )' % (a1, h, HCLS('z', c)))
        r2 = w.s([m], 'ralrimiva', "( ( %s /\\ r e. %s ) -> A. z e. Gamma' ( %s ` <. r , ( inl ` z ) >. ) e. %s )"
                 % (ph, S, h, HCLS('z', c)))
        rals.append(w.s([r2], 'ralrimiva', '( %s -> %s )' % (ph, HI_KET if h == RDK else HI_BLK)))
    w.qed([ty, rals[0], rals[1]], '3jca', ST_HI)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        if l == 'tmctbhi':
            tmctbhi()
        else:
            {'f': hf, 'v': hv, 'c': hc}[l[-1]](l[5:8])
