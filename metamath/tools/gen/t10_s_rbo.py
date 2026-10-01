"""T10: the peek handler ` readBraOr ` (df-tmrdbror, Lean ` peekBraOr ` 's handler) and its peek interface.

  tmrdbrorf   ` readBraOr ` is a function on the states and the peeked symbols
  tmrdbrorv   its value: ` flag := v.flag || decide ( o = some bra ) `
  tmrdbrorc   at ` inl Z ` the state lands in the class of states whose flag is ` ( v.flag = 1 \\/ Z = bra ) `

    MM_DB=sorties/t10.mm python3 tools/gen/t10_s_rbo.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t10lib import *
from t7lib import tuple_facts, st_comps, rab_in, _transport
import t8alib as A8

SEL = sys.argv[1:]
IFO = lambda v, o: 'if ( ( ( TMfl ` %s ) = 1o \\/ %s = ( inl ` 2 ) ) , 1o , (/) )' % (v, o)
ST_F = '%s e. %s' % (RBO, HDLC)
ST_V = '( ( V e. TMSt /\\ O e. %s ) -> ( %s ` <. V , O >. ) = %s )' % (OPT, RBO, RBO_EVAL('V', 'O'))
CLS_C = A8.NFL('if ( ( ( TMfl ` V ) = 1o \\/ Z = 2 ) , 1o , (/) )')
ST_C = "( ( V e. TMSt /\\ Z e. Gamma' ) -> ( %s ` <. V , ( inl ` Z ) >. ) e. %s )" % (RBO, CLS_C)


def ifo_cl(w, ph, v, o):
    s = w.s
    return s([s([s([], '1oel2o', '1o e. 2o'), s([], '0el2o', '(/) e. 2o')], 'ifcli', '%s e. 2o' % IFO(v, o))], 'a1i',
             '( %s -> %s e. 2o )' % (ph, IFO(v, o)))


def tmrdbrorf():
    lab = 'tmrdbrorf'
    w = W(lab, 'The handler ` readBraOr ` is a function on the states and the peeked symbols (Lean: its type '
               '` St -> Option Gamma\' -> St ` ).')
    ph = '( v e. TMSt /\\ o e. %s )' % OPT
    vv = w.s([], 'simpl', '( %s -> v e. TMSt )' % ph)
    cl = st_comps(w, ph, 'v', vv)
    comps = [FLD(f, 'v') for f in ORDER[:6]] + [IFO('v', 'o')]
    cls = [cl[f] for f in ORDER[:6]] + [ifo_cl(w, ph, 'v', 'o')]
    mem, _ = tuple_facts(w, ph, comps, cls)
    B = RBO_EVAL('v', 'o')
    ral = w.s([mem], 'rgen2', 'A. v e. TMSt A. o e. %s %s e. TMSt' % (OPT, B))
    d = w.s([], 'df-tmrdbror', DF_RBO)
    fm = w.s([d], 'fmpo', '( A. v e. TMSt A. o e. %s %s e. TMSt <-> %s : ( TMSt X. %s ) --> TMSt )' % (OPT, B, RBO, OPT))
    ff = w.s([ral, fm], 'mpbi', '%s : ( TMSt X. %s ) --> TMSt' % (RBO, OPT))
    sv = w.s([w.s([], 'tmstfi', 'TMSt e. Fin')], 'elexi', 'TMSt e. _V')
    ov = w.s([w.s([], 'gammaex', "Gamma' e. _V"), w.s([], '1oex', '1o e. _V'), w.inst('djuex')], 'mp2an', '%s e. _V' % OPT)
    xv = w.s([sv, ov, w.inst('xpexg')], 'mp2an', '( TMSt X. %s ) e. _V' % OPT)
    em = w.s([sv, xv, w.inst('elmapg')], 'mp2an', '( %s e. %s <-> %s : ( TMSt X. %s ) --> TMSt )' % (RBO, HDLC, RBO, OPT))
    w.qed([ff, em], 'mpbir', ST_F)
    return w.run()


def tmrdbrorv():
    lab = 'tmrdbrorv'
    w = W(lab, 'Value of ` readBraOr ` : the flag becomes ` v.flag || decide ( o = some bra ) ` , the other fields stay '
               '(Lean ` peekBraOr ` ).')
    ph = '( V e. TMSt /\\ O e. %s )' % OPT
    vv = w.s([], 'simpl', '( %s -> V e. TMSt )' % ph)
    oo = w.s([], 'simpr', '( %s -> O e. %s )' % (ph, OPT))
    B = RBO_EVAL('v', 'o'); BV = RBO_EVAL('V', 'O')
    ante = '( v = V /\\ o = O )'
    ev = w.s([], 'simpl', '( %s -> v = V )' % ante)
    eo = w.s([], 'simpr', '( %s -> o = O )' % ante)
    cg, nb = w.congr(B, {'v': 'V', 'o': 'O'}, ante, {'v': ev, 'o': eo})
    assert nb == BV, nb
    d = w.s([], 'df-tmrdbror', DF_RBO)
    bxa = w.s([w.s([], 'opex', '%s e. _V' % BV)], 'a1i', '( %s -> %s e. _V )' % (ph, BV))
    j = w.s([vv, oo, bxa], '3jca', '( %s -> ( V e. TMSt /\\ O e. %s /\\ %s e. _V ) )' % (ph, OPT, BV))
    ovi = w.s([cg, d], 'ovmpoga', '( ( V e. TMSt /\\ O e. %s /\\ %s e. _V ) -> ( V %s O ) = %s )' % (OPT, BV, RBO, BV))
    ov = w.s([j, ovi], 'syl', '( %s -> ( V %s O ) = %s )' % (ph, RBO, BV))
    dova = w.s([w.s([], 'df-ov', '( V %s O ) = ( %s ` <. V , O >. )' % (RBO, RBO))], 'a1i',
               '( %s -> ( V %s O ) = ( %s ` <. V , O >. ) )' % (ph, RBO, RBO))
    w.qed([dova, ov], 'eqtr3d', ST_V)
    return w.run()


def tmrdbrorc():
    lab = 'tmrdbrorc'
    w = W(lab, 'Lean\'s ` peekBraOr_runs ` at a state: ` readBraOr ` on the symbol ` Z ` sets the flag to '
               '` v.flag || decide ( Z = bra ) ` ; the state lands in the class of states whose flag is that value.')
    s = w.s
    ph = "( V e. TMSt /\\ Z e. Gamma' )"
    vv = s([], 'simpl', '( %s -> V e. TMSt )' % ph)
    zg = s([], 'simpr', "( %s -> Z e. Gamma' )" % ph)
    O = '( inl ` Z )'
    oz = s([zg, w.inst('djulcl')], 'syl', '( %s -> %s e. %s )' % (ph, O, OPT))
    N = '( %s ` <. V , %s >. )' % (RBO, O)
    comps = [FLD(f, 'V') for f in ORDER[:6]] + [IFO('V', O)]
    val = s([vv, oz, w.inst('tmrdbrorv')], 'syl2anc', '( %s -> %s = %s )' % (ph, N, MK(*comps)))
    cl = st_comps(w, ph, 'V', vv)
    cls = [cl[f] for f in ORDER[:6]] + [ifo_cl(w, ph, 'V', O)]
    mem, vals = tuple_facts(w, ph, comps, cls)
    nv = _transport(w, ph, N, val, mem, vals, comps)
    i11 = s([s([zg], 'elexd', '( %s -> Z e. _V )' % ph), closed(w, ph, '2ex', '2 e. _V'), w.inst('tmcinl11')], 'syl2anc',
            '( %s -> ( %s = ( inl ` 2 ) <-> Z = 2 ) )' % (ph, O))
    ob = s([i11], 'orbi2d', '( %s -> ( ( ( TMfl ` V ) = 1o \\/ %s = ( inl ` 2 ) ) <-> ( ( TMfl ` V ) = 1o \\/ Z = 2 ) ) )' % (ph, O))
    V1 = 'if ( ( ( TMfl ` V ) = 1o \\/ Z = 2 ) , 1o , (/) )'
    ib = s([ob], 'ifbid', '( %s -> %s = %s )' % (ph, IFO('V', O), V1))
    fl = s([nv['fields']['fl'], ib], 'eqtrd', '( %s -> ( TMfl ` %s ) = %s )' % (ph, N, V1))
    rab_in(w, ph, CLS_C, lambda t: '( TMfl ` %s ) = %s' % (t, V1), N, nv['mem'], fl)
    w.lines[-1] = 'qed:' + w.lines[-1].split(':', 1)[1]
    return w.run()


# ------------------------------------------------------------ the peek interface in proofs
def rbo_ty(w, ps, mk):
    """( ps -> TMrdBraOr e. HDLS )"""
    s = w.s
    seqr = s([mk['seq']], 'eqcomd', '( %s -> TMSt = %s )' % (ps, S))
    x1 = s([seqr], 'xpeq1d', "( %s -> ( TMSt X. ( Gamma' |_| 1o ) ) = ( %s X. ( Gamma' |_| 1o ) ) )" % (ps, S))
    e3 = s([seqr, x1], 'oveq12d', '( %s -> %s = %s )' % (ps, HDLC, A8.HDLS))
    return s([closed(w, ps, 'tmrdbrorf', ST_F), e3], 'eleqtrd', '( %s -> %s e. %s )' % (ps, RBO, A8.HDLS))


def rbo_iface(w, ph, mk, V0, Z, zg, bi, CND):
    """( ph -> A. r e. NFL( V0 ) ( TMrdBraOr ` <. r , ( inl ` Z ) >. ) e. NFL( if ( CND , 1o , (/) ) ) ) from
    zg : ( ph -> Z e. Gamma' ) and bi : ( ph -> ( ( V0 = 1o \\/ Z = 2 ) <-> CND ) ) (ph free of r)"""
    s = w.s
    a = '( %s /\\ r e. %s )' % (ph, A8.NFL(V0))
    L = lambda st: s([st], 'adantr', '( %s -> %s )' % (a, concl(w, ph, st)))
    rr, rf = A8.nfl_unpack(w, a, V0, 'r', s([], 'simpr', '( %s -> r e. %s )' % (a, A8.NFL(V0))))
    N = '( %s ` <. r , ( inl ` %s ) >. )' % (RBO, Z)
    V1r = 'if ( ( ( TMfl ` r ) = 1o \\/ %s = 2 ) , 1o , (/) )' % Z
    m = s([rr, L(zg), w.inst('tmrdbrorc')], 'syl2anc', '( %s -> %s e. %s )' % (a, N, A8.NFL(V1r)))
    nm, nf = A8.nfl_unpack(w, a, V1r, N, m)
    e1 = s([rf], 'eqeq1d', '( %s -> ( ( TMfl ` r ) = 1o <-> %s = 1o ) )' % (a, V0))
    o1 = s([e1], 'orbi1d', '( %s -> ( ( ( TMfl ` r ) = 1o \\/ %s = 2 ) <-> ( %s = 1o \\/ %s = 2 ) ) )' % (a, Z, V0, Z))
    o2 = s([o1, L(bi)], 'bitrd', '( %s -> ( ( ( TMfl ` r ) = 1o \\/ %s = 2 ) <-> %s ) )' % (a, Z, CND))
    V2 = 'if ( %s , 1o , (/) )' % CND
    f2 = s([nf, s([o2], 'ifbid', '( %s -> %s = %s )' % (a, V1r, V2))], 'eqtrd', '( %s -> ( TMfl ` %s ) = %s )' % (a, N, V2))
    p = A8.nfl_pack(w, a, V2, N, nm, f2)
    return s([p], 'ralrimiva', '( %s -> A. r e. %s %s e. %s )' % (ph, A8.NFL(V0), N, A8.NFL(V2)))


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
