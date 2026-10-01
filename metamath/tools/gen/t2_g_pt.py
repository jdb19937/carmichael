"""T2: `pushTerm` of TM/Prims.lean --- a chain of pushes at one label per
symbol, as an instantiation of `tm2hitr` (blueprint 3.3)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t1lib import *
from t2_c_mov import constfty, DG, GK, ST, STMT_T

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

NW = '( # ` W )'
def LB(x): return '( I ` %s )' % x
def PGM(x):
    return PUSH('K', CONSTF('T', '( W ` %s )' % x), GOTO(CONSTF('T', LB('( %s + 1 )' % x))))
HPROG = 'A. k e. ( 0 ..^ %s ) ( M ` %s ) = %s' % (NW, LB('k'), PGM('k'))
KDW = '( K e. %s /\\ D e. %s /\\ W e. Word %s )' % (DG, STK('T'), GK)
ITY = 'I : ( 0 ... %s ) --> %s' % (NW, L('T'))
PHP = '( %s /\\ %s /\\ ( %s /\\ %s ) )' % (PHM, KDW, ITY, HPROG)
DK = '( D ` K )'
def PRE(x): return '( ( reverse ` ( W prefix %s ) ) ++ %s )' % (x, DK)
def CLP(x): return '( { ( inl ` %s ) } X. ( %s X. { %s } ) )' % (LB(x), S('T'), UPD('T', 'D', 'K', PRE(x)))
IF = ('( j e. NN0 |-> ( { ( inl ` %s ) } X. ( %s X. { %s } ) ) )'
      % (LB('j'), S('T'), UPD('T', 'D', 'K', PRE('j'))))


def ctx(w, ph, lift=None):
    def g(ref, f):
        st = w.s([], ref, '( %s -> %s )' % (PHP, f))
        return w.s([st], lift, '( %s -> %s )' % (ph, f)) if lift else st
    phm = g('simp1', PHM)
    kdw = g('simp2', KDW)
    p3 = g('simp3', '( %s /\\ %s )' % (ITY, HPROG))
    kk = w.s([kdw, w.inst('simp1')], 'syl', '( %s -> K e. %s )' % (ph, DG))
    dd = w.s([kdw, w.inst('simp2')], 'syl', '( %s -> D e. %s )' % (ph, STK('T')))
    ww = w.s([kdw, w.inst('simp3')], 'syl', '( %s -> W e. Word %s )' % (ph, GK))
    ity = w.s([p3], 'simpld', '( %s -> %s )' % (ph, ITY))
    hpg = w.s([p3], 'simprd', '( %s -> %s )' % (ph, HPROG))
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    dkw = w.s([tv, dd, kk, w.inst('tm2stkfv')], 'syl3anc', '( %s -> %s e. Word %s )' % (ph, DK, GK))
    return dict(phm=phm, kk=kk, dd=dd, ww=ww, ity=ity, hpg=hpg, tv=tv, dkw=dkw)


def prew(w, ante, X, wwd, dkw):
    """( ante -> PRE(X) e. Word GK )"""
    p = w.s([wwd, w.inst('pfxcl')], 'syl', '( %s -> ( W prefix %s ) e. Word %s )' % (ante, X, GK))
    r = w.s([p, w.inst('revcl')], 'syl', '( %s -> ( reverse ` ( W prefix %s ) ) e. Word %s )' % (ante, X, GK))
    return w.s([r, dkw, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word %s )' % (ante, PRE(X), GK))


def clpss(w, ante, X, tv, lcl, updcl):
    sn = w.s([updcl], 'snssd', '( %s -> { %s } C_ %s )' % (ante, UPD('T', 'D', 'K', PRE(X)), STK('T')))
    ssr = w.s([], 'ssid', '%s C_ %s' % (S('T'), S('T')))
    ssra = w.s([ssr], 'a1i', '( %s -> %s C_ %s )' % (ante, S('T'), S('T')))
    xs = w.s([ssra, sn, w.inst('xpss12')], 'syl2anc',
             '( %s -> ( %s X. { %s } ) C_ %s )' % (ante, S('T'), UPD('T', 'D', 'K', PRE(X)), ST))
    return w.s([tv, lcl, xs, w.inst('tm2hcfgss')], 'syl3anc', '( %s -> %s C_ %s )' % (ante, CLP(X), CFG('T')))


def ifval(w, ante, X, xcl, updcl):
    """( ante -> ( IF ` X ) = CLP(X) ) for xcl : X e. NN0"""
    aq = '( %s /\\ j = %s )' % (ante, X)
    lj = w.s([], 'simpr', '( %s -> j = %s )' % (aq, X))
    body = ('( { ( inl ` %s ) } X. ( %s X. { %s } ) )'
            % (LB('j'), S('T'), UPD('T', 'D', 'K', PRE('j'))))
    st, res = W.congr(w, body, {'j': X}, aq, {'j': lj})
    assert res == CLP(X), res
    eqi = w.s([], 'eqid', '%s = %s' % (IF, IF))
    xv = w.s([xcl], 'elexd', '( %s -> %s e. _V )' % (ante, X))
    a = w.s([], 'snex', '{ ( inl ` %s ) } e. _V' % LB(X))
    b = w.s([], 'fvex', '%s e. _V' % S('T'))
    c = w.s([], 'snex', '{ %s } e. _V' % UPD('T', 'D', 'K', PRE(X)))
    d = w.s([b, c], 'xpex', '( %s X. { %s } ) e. _V' % (S('T'), UPD('T', 'D', 'K', PRE(X))))
    e = w.s([a, d], 'xpex', '%s e. _V' % CLP(X))
    ea = w.s([e], 'a1i', '( %s -> %s e. _V )' % (ante, CLP(X)))
    return w.s([st, eqi, xcl, ea], 'fvmptd2', '( %s -> ( %s ` %s ) = %s )' % (ante, IF, X, CLP(X)))


def tm2fpt():
    lab = 'tm2fpt'
    ph = PHP
    pi = '( %s /\\ i e. ( 0 ..^ %s ) )' % (ph, NW)
    w = W(lab, 'The fragment ` pushTerm ` of TM/Prims.lean: a chain of '
               '` ( # ` W ) ` pushes, one label per symbol, pushes the word '
               '` W ` onto stack ` K ` (so that the last symbol pushed is on '
               'top).  An instantiation of ~ tm2hitr over the position, with '
               'the label family ` I ` and the invariant carrying the prefix '
               'pushed so far; Lean\'s ` pushTerm_runs ` does the same '
               'induction by hand over the list.')
    u = ctx(w, ph)
    # --- the iteration hypothesis
    ui = ctx(w, pi, 'adantr')
    ii = w.s([], 'simpr', '( %s -> i e. ( 0 ..^ %s ) )' % (pi, NW))
    inn = w.s([ii, w.inst('elfzonn0')], 'syl', '( %s -> i e. NN0 )' % pi)
    i1n = w.s([inn, w.inst('peano2nn0')], 'syl', '( %s -> ( i + 1 ) e. NN0 )' % pi)
    ifz = w.s([ii, w.inst('elfzofz')], 'syl', '( %s -> i e. ( 0 ... %s ) )' % (pi, NW))
    nwn = w.s([ui['ww'], w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (pi, NW))
    ile = w.s([ii, w.inst('elfzop1le2')], 'syl', '( %s -> ( i + 1 ) <_ %s )' % (pi, NW))
    i1fz0 = w.s([i1n, nwn, ile], '3jca', '( %s -> ( ( i + 1 ) e. NN0 /\\ %s e. NN0 /\\ ( i + 1 ) <_ %s ) )'
                % (pi, NW, NW))
    i1fz = w.s([i1fz0, w.inst('elfz2nn0')], 'sylibr', '( %s -> ( i + 1 ) e. ( 0 ... %s ) )' % (pi, NW))
    # the labels
    ail = w.s([ui['ity'], ifz], 'ffvelcdmd', '( %s -> %s e. %s )' % (pi, LB('i'), L('T')))
    eil = w.s([ui['ity'], i1fz], 'ffvelcdmd', '( %s -> %s e. %s )' % (pi, LB('( i + 1 )'), L('T')))
    # the program at i
    n1 = w.s([], 'fveq2', '( k = i -> %s = %s )' % (LB('k'), LB('i')))
    n2 = w.s([n1], 'fveq2d', '( k = i -> ( M ` %s ) = ( M ` %s ) )' % (LB('k'), LB('i')))
    n3 = w.s([], 'fveq2', '( k = i -> ( W ` k ) = ( W ` i ) )')
    n4 = w.s([n3], 'sneqd', '( k = i -> { ( W ` k ) } = { ( W ` i ) } )')
    n5 = w.s([n4], 'xpeq2d', '( k = i -> %s = %s )'
             % (CONSTF('T', '( W ` k )'), CONSTF('T', '( W ` i )')))
    n6 = w.s([], 'oveq1', '( k = i -> ( k + 1 ) = ( i + 1 ) )')
    n7 = w.s([n6], 'fveq2d', '( k = i -> %s = %s )' % (LB('( k + 1 )'), LB('( i + 1 )')))
    n8 = w.s([n7], 'sneqd', '( k = i -> { %s } = { %s } )' % (LB('( k + 1 )'), LB('( i + 1 )')))
    n9 = w.s([n8], 'xpeq2d', '( k = i -> %s = %s )'
             % (CONSTF('T', LB('( k + 1 )')), CONSTF('T', LB('( i + 1 )'))))
    n10 = w.s([n9], 'opeq2d', '( k = i -> %s = %s )'
              % (GOTO(CONSTF('T', LB('( k + 1 )'))), GOTO(CONSTF('T', LB('( i + 1 )')))))
    n11 = w.s([n5, n10], 'opeq12d', '( k = i -> <. %s , %s >. = <. %s , %s >. )'
              % (CONSTF('T', '( W ` k )'), GOTO(CONSTF('T', LB('( k + 1 )'))),
                 CONSTF('T', '( W ` i )'), GOTO(CONSTF('T', LB('( i + 1 )')))))
    n12 = w.s([n11], 'opeq2d', '( k = i -> <. K , <. %s , %s >. >. = <. K , <. %s , %s >. >. )'
              % (CONSTF('T', '( W ` k )'), GOTO(CONSTF('T', LB('( k + 1 )'))),
                 CONSTF('T', '( W ` i )'), GOTO(CONSTF('T', LB('( i + 1 )')))))
    n13 = w.s([n12], 'opeq2d', '( k = i -> %s = %s )' % (PGM('k'), PGM('i')))
    n14 = w.s([n2, n13], 'eqeq12d', '( k = i -> ( ( M ` %s ) = %s <-> ( M ` %s ) = %s ) )'
              % (LB('k'), PGM('k'), LB('i'), PGM('i')))
    meq = w.s([n14, ui['hpg'], ii], 'rspcdva', '( %s -> ( M ` %s ) = %s )' % (pi, LB('i'), PGM('i')))
    # the two stack contents
    prei = prew(w, pi, 'i', ui['ww'], ui['dkw'])
    prei1 = prew(w, pi, '( i + 1 )', ui['ww'], ui['dkw'])
    ki = w.s([ui['kk'], prei], 'jca', '( %s -> ( K e. %s /\\ %s e. Word %s ) )' % (pi, DG, PRE('i'), GK))
    ki1 = w.s([ui['kk'], prei1], 'jca', '( %s -> ( K e. %s /\\ %s e. Word %s ) )' % (pi, DG, PRE('( i + 1 )'), GK))
    d1cl = w.s([ui['tv'], ui['dd'], ki, w.inst('tm2stkupd')], 'syl3anc',
               '( %s -> %s e. %s )' % (pi, UPD('T', 'D', 'K', PRE('i')), STK('T')))
    d2cl = w.s([ui['tv'], ui['dd'], ki1, w.inst('tm2stkupd')], 'syl3anc',
               '( %s -> %s e. %s )' % (pi, UPD('T', 'D', 'K', PRE('( i + 1 )')), STK('T')))
    wi = w.s([ui['ww'], ii, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> ( W ` i ) e. %s )' % (pi, GK))
    fwi = constfty(w, pi, '( W ` i )', GK, wi)
    fli = constfty(w, pi, LB('( i + 1 )'), L('T'), eil)
    gt = w.s([ui['tv'], fli, w.inst('tm2goto')], 'syl2anc',
             '( %s -> %s e. %s )' % (pi, GOTO(CONSTF('T', LB('( i + 1 )'))), STMT_T))
    # the prefix step
    ir = w.s([inn, w.inst('nn0red')], 'syl', '( %s -> i e. RR )' % pi)
    ilp = w.s([ir, w.inst('lep1')], 'syl', '( %s -> i <_ ( i + 1 ) )' % pi)
    ifz1 = w.s([w.s([inn, i1n, ilp], '3jca',
                    '( %s -> ( i e. NN0 /\\ ( i + 1 ) e. NN0 /\\ i <_ ( i + 1 ) ) )' % pi),
                w.inst('elfz2nn0')], 'sylibr', '( %s -> i e. ( 0 ... ( i + 1 ) ) )' % pi)
    cp = w.s([ui['ww'], ifz1, i1fz, w.inst('ccatpfx')], 'syl3anc',
             '( %s -> ( ( W prefix i ) ++ ( W substr <. i , ( i + 1 ) >. ) ) = ( W prefix ( i + 1 ) ) )' % pi)
    sw = w.s([ui['ww'], ii, w.inst('swrds1')], 'syl2anc',
             '( %s -> ( W substr <. i , ( i + 1 ) >. ) = <" ( W ` i ) "> )' % pi)
    cp2, cpn = w.rewrite('( ( W prefix i ) ++ ( W substr <. i , ( i + 1 ) >. ) )',
                         {'( W substr <. i , ( i + 1 ) >. )': ('<" ( W ` i ) ">', sw)}, pi)
    cpc = w.s([cp2], 'eqcomd', '( %s -> ( ( W prefix i ) ++ <" ( W ` i ) "> ) = ( ( W prefix i ) ++ ( W substr <. i , ( i + 1 ) >. ) ) )' % pi)
    cpx = w.s([cpc, cp], 'eqtrd', '( %s -> ( ( W prefix i ) ++ <" ( W ` i ) "> ) = ( W prefix ( i + 1 ) ) )' % pi)
    pfi = w.s([ui['ww'], w.inst('pfxcl')], 'syl', '( %s -> ( W prefix i ) e. Word %s )' % (pi, GK))
    s1i = w.s([wi], 's1cld', '( %s -> <" ( W ` i ) "> e. Word %s )' % (pi, GK))
    rv = w.s([pfi, s1i, w.inst('revccat')], 'syl2anc',
             '( %s -> ( reverse ` ( ( W prefix i ) ++ <" ( W ` i ) "> ) ) = ( ( reverse ` <" ( W ` i ) "> ) ++ ( reverse ` ( W prefix i ) ) )' % pi + ' )')
    rs1 = w.s([], 'revs1', '( reverse ` <" ( W ` i ) "> ) = <" ( W ` i ) ">')
    rs1a = w.s([rs1], 'a1i', '( %s -> ( reverse ` <" ( W ` i ) "> ) = <" ( W ` i ) "> )' % pi)
    rv2, rvn = w.rewrite('( ( reverse ` <" ( W ` i ) "> ) ++ ( reverse ` ( W prefix i ) ) )',
                         {'( reverse ` <" ( W ` i ) "> )': ('<" ( W ` i ) ">', rs1a)}, pi)
    rv3 = w.s([rv, rv2], 'eqtrd',
              '( %s -> ( reverse ` ( ( W prefix i ) ++ <" ( W ` i ) "> ) ) = ( <" ( W ` i ) "> ++ ( reverse ` ( W prefix i ) ) ) )' % pi)
    rvi = w.s([cpx], 'fveq2d',
              '( %s -> ( reverse ` ( ( W prefix i ) ++ <" ( W ` i ) "> ) ) = ( reverse ` ( W prefix ( i + 1 ) ) ) )' % pi)
    rvfin = w.s([rvi, rv3], 'eqtr3d',
                '( %s -> ( reverse ` ( W prefix ( i + 1 ) ) ) = ( <" ( W ` i ) "> ++ ( reverse ` ( W prefix i ) ) ) )' % pi)
    rvpi = w.s([pfi, w.inst('revcl')], 'syl', '( %s -> ( reverse ` ( W prefix i ) ) e. Word %s )' % (pi, GK))
    asso = w.s([s1i, rvpi, ui['dkw'], w.inst('ccatass')], 'syl3anc',
               '( %s -> ( ( <" ( W ` i ) "> ++ ( reverse ` ( W prefix i ) ) ) ++ %s ) = ( <" ( W ` i ) "> ++ %s ) )'
               % (pi, DK, PRE('i')))
    pre1 = w.s([rvfin], 'oveq1d',
               '( %s -> %s = ( ( <" ( W ` i ) "> ++ ( reverse ` ( W prefix i ) ) ) ++ %s ) )'
               % (pi, PRE('( i + 1 )'), DK))
    pre2 = w.s([pre1, asso], 'eqtrd', '( %s -> %s = ( <" ( W ` i ) "> ++ %s ) )' % (pi, PRE('( i + 1 )'), PRE('i')))
    pre2c = w.s([pre2], 'eqcomd', '( %s -> ( <" ( W ` i ) "> ++ %s ) = %s )' % (pi, PRE('i'), PRE('( i + 1 )')))

    def body(av):
        def A_(st, f): return w.s([st], 'adantr', '( %s -> %s )' % (av, f))
        tv = A_(ui['tv'], 'T e. V')
        vv = w.s([], 'simpr', '( %s -> v e. %s )' % (av, S('T')))
        kk = A_(ui['kk'], 'K e. %s' % DG); dd = A_(ui['dd'], 'D e. %s' % STK('T'))
        d1 = A_(d1cl, '%s e. %s' % (UPD('T', 'D', 'K', PRE('i')), STK('T')))
        d2 = A_(d2cl, '%s e. %s' % (UPD('T', 'D', 'K', PRE('( i + 1 )')), STK('T')))
        fwia = A_(fwi, '%s e. ( %s ^m %s )' % (CONSTF('T', '( W ` i )'), GK, S('T')))
        flia = A_(fli, '%s e. ( %s ^m %s )' % (CONSTF('T', LB('( i + 1 )')), L('T'), S('T')))
        gta = A_(gt, '%s e. %s' % (GOTO(CONSTF('T', LB('( i + 1 )'))), STMT_T))
        wia = A_(wi, '( W ` i ) e. %s' % GK)
        eila = A_(eil, '%s e. %s' % (LB('( i + 1 )'), L('T')))
        preia = A_(prei, '%s e. Word %s' % (PRE('i'), GK))
        prei1a = A_(prei1, '%s e. Word %s' % (PRE('( i + 1 )'), GK))
        pre2ca = A_(pre2c, '( <" ( W ` i ) "> ++ %s ) = %s' % (PRE('i'), PRE('( i + 1 )')))
        prev = w.s([preia], 'elexd', '( %s -> %s e. _V )' % (av, PRE('i')))
        rk = updkval(w, av, 'T', 'D', 'K', PRE('i'), tv, dd, kk, prev)
        wiv = w.s([wia], 'elexd', '( %s -> ( W ` i ) e. _V )' % av)
        fcw = w.s([wiv, vv, w.inst('fvconst2g')], 'syl2anc',
                  '( %s -> ( %s ` v ) = ( W ` i ) )' % (av, CONSTF('T', '( W ` i )')))
        eilv = w.s([eila], 'elexd', '( %s -> %s e. _V )' % (av, LB('( i + 1 )')))
        fcl = w.s([eilv, vv, w.inst('fvconst2g')], 'syl2anc',
                  '( %s -> ( %s ` v ) = %s )' % (av, CONSTF('T', LB('( i + 1 )')), LB('( i + 1 )')))
        p1 = w.s([tv, dd], 'jca', '( %s -> ( T e. V /\\ D e. %s ) )' % (av, STK('T')))
        p2 = w.s([preia, prei1a], 'jca', '( %s -> ( %s e. Word %s /\\ %s e. Word %s ) )'
                 % (av, PRE('i'), GK, PRE('( i + 1 )'), GK))
        col = w.s([p1, kk, p2, w.inst('tm2stkup2')], 'syl3anc',
                  '( %s -> %s = %s )'
                  % (av, UPD('T', UPD('T', 'D', 'K', PRE('i')), 'K', PRE('( i + 1 )')),
                     UPD('T', 'D', 'K', PRE('( i + 1 )'))))
        facts = {'T e. V': tv, 'v e. %s' % S('T'): vv, 'K e. %s' % DG: kk,
                 '%s e. %s' % (UPD('T', 'D', 'K', PRE('i')), STK('T')): d1,
                 '%s e. %s' % (UPD('T', 'D', 'K', PRE('( i + 1 )')), STK('T')): d2,
                 '%s e. ( %s ^m %s )' % (CONSTF('T', '( W ` i )'), GK, S('T')): fwia,
                 '%s e. ( %s ^m %s )' % (CONSTF('T', LB('( i + 1 )')), L('T'), S('T')): flia,
                 '%s e. %s' % (GOTO(CONSTF('T', LB('( i + 1 )'))), STMT_T): gta}
        rules = {'( %s ` v )' % CONSTF('T', '( W ` i )'): ('( W ` i )', fcw),
                 '( %s ` K )' % UPD('T', 'D', 'K', PRE('i')): (PRE('i'), rk),
                 '( <" ( W ` i ) "> ++ %s )' % PRE('i'): (PRE('( i + 1 )'), pre2ca),
                 UPD('T', UPD('T', 'D', 'K', PRE('i')), 'K', PRE('( i + 1 )')):
                     (UPD('T', 'D', 'K', PRE('( i + 1 )')), col),
                 '( %s ` v )' % CONSTF('T', LB('( i + 1 )')): (LB('( i + 1 )'), fcl)}
        ex = Exec(w, av, 'T', facts, rules=rules)
        st, res = ex.run(PGM('i'), '<. v , %s >.' % UPD('T', 'D', 'K', PRE('i')))
        want_res = ('<. ( inl ` %s ) , <. v , %s >. >.'
                    % (LB('( i + 1 )'), UPD('T', 'D', 'K', PRE('( i + 1 )'))))
        assert res == want_res, 'GOT %s\nWANT %s' % (res, want_res)
        meqa = A_(meq, '( M ` %s ) = %s' % (LB('i'), PGM('i')))
        o1 = w.s([meqa], 'oveq1d', '( %s -> ( ( M ` %s ) %s <. v , %s >. ) = ( %s %s <. v , %s >. ) )'
                 % (av, LB('i'), SA('T'), UPD('T', 'D', 'K', PRE('i')), PGM('i'), SA('T'),
                    UPD('T', 'D', 'K', PRE('i'))))
        fin = w.s([o1, st], 'eqtrd', '( %s -> ( ( M ` %s ) %s <. v , %s >. ) = %s )'
                  % (av, LB('i'), SA('T'), UPD('T', 'D', 'K', PRE('i')), res))
        return fin, 'v', vv
    tri, C1, C2 = hstepc(w, pi, 'T', 'M', LB('i'), LB('( i + 1 )'),
                         UPD('T', 'D', 'K', PRE('i')), UPD('T', 'D', 'K', PRE('( i + 1 )')),
                         (meq, ui['phm']), ail, eil, d1cl, d2cl, body)
    assert C1 == CLP('i') and C2 == CLP('( i + 1 )'), (C1, C2)
    # transport to the family
    jvi = ifval(w, pi, 'i', inn, d1cl)
    jvi1 = ifval(w, pi, '( i + 1 )', i1n, d2cl)
    b1 = w.s([jvi1], 'opeq1d', '( %s -> <. %s , 1 >. = <. %s , 1 >. )'
             % (pi, '( %s ` ( i + 1 ) )' % IF, CLP('( i + 1 )')))
    b2 = w.s([b1], 'breq2d', '( %s -> ( %s <-> %s ) )'
             % (pi, HR(CLP('i'), 'T', 'M', '( %s ` ( i + 1 ) )' % IF, '1'),
                HR(CLP('i'), 'T', 'M', CLP('( i + 1 )'), '1')))
    t1 = w.s([b2, tri], 'mpbird', '( %s -> %s )'
             % (pi, HR(CLP('i'), 'T', 'M', '( %s ` ( i + 1 ) )' % IF, '1')))
    b3 = w.s([jvi], 'breq1d', '( %s -> ( %s <-> %s ) )'
             % (pi, HR('( %s ` i )' % IF, 'T', 'M', '( %s ` ( i + 1 ) )' % IF, '1'),
                HR(CLP('i'), 'T', 'M', '( %s ` ( i + 1 ) )' % IF, '1')))
    t2 = w.s([b3, t1], 'mpbird', '( %s -> %s )'
             % (pi, HR('( %s ` i )' % IF, 'T', 'M', '( %s ` ( i + 1 ) )' % IF, '1')))
    HYP = ('A. i e. ( 0 ..^ %s ) %s'
           % (NW, HR('( %s ` i )' % IF, 'T', 'M', '( %s ` ( i + 1 ) )' % IF, '1')))
    hyp = w.s([t2], 'ralrimiva', '( %s -> %s )' % (ph, HYP))
    # ( IF ` 0 ) C_ Cfg
    z0 = w.s([], '0nn0', '0 e. NN0')
    z0a = w.s([z0], 'a1i', '( %s -> 0 e. NN0 )' % ph)
    pre0 = prew(w, ph, '0', u['ww'], u['dkw'])
    k0 = w.s([u['kk'], pre0], 'jca', '( %s -> ( K e. %s /\\ %s e. Word %s ) )' % (ph, DG, PRE('0'), GK))
    d0cl = w.s([u['tv'], u['dd'], k0, w.inst('tm2stkupd')], 'syl3anc',
               '( %s -> %s e. %s )' % (ph, UPD('T', 'D', 'K', PRE('0')), STK('T')))
    nwn2 = w.s([u['ww'], w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, NW))
    z0fz = w.s([w.s([z0a, nwn2, w.s([nwn2, w.inst('nn0ge0')], 'syl', '( %s -> 0 <_ %s )' % (ph, NW))],
                    '3jca', '( %s -> ( 0 e. NN0 /\\ %s e. NN0 /\\ 0 <_ %s ) )' % (ph, NW, NW)),
                w.inst('elfz2nn0')], 'sylibr', '( %s -> 0 e. ( 0 ... %s ) )' % (ph, NW))
    l0 = w.s([u['ity'], z0fz], 'ffvelcdmd', '( %s -> %s e. %s )' % (ph, LB('0'), L('T')))
    ss0 = clpss(w, ph, '0', u['tv'], l0, d0cl)
    jv0 = ifval(w, ph, '0', z0a, d0cl)
    ss0j = w.s([jv0, ss0], 'eqsstrd', '( %s -> ( %s ` 0 ) C_ %s )' % (ph, IF, CFG('T')))
    # tm2hitr
    n1a = w.s([], '1nn0', '1 e. NN0')
    n1b = w.s([n1a], 'a1i', '( %s -> 1 e. NN0 )' % ph)
    pj = w.s([ss0j, n1b], 'jca', '( %s -> ( ( %s ` 0 ) C_ %s /\\ 1 e. NN0 ) )' % (ph, IF, CFG('T')))
    ant = w.s([u['phm'], pj, hyp], '3jca',
              '( %s -> ( %s /\\ ( ( %s ` 0 ) C_ %s /\\ 1 e. NN0 ) /\\ %s ) )' % (ph, PHM, IF, CFG('T'), HYP))
    itr0 = w.s([nwn2, w.inst('tm2hitr')], 'syl',
               '( %s -> ( ( %s /\\ ( ( %s ` 0 ) C_ %s /\\ 1 e. NN0 ) /\\ %s ) -> %s ) )'
               % (ph, PHM, IF, CFG('T'), HYP,
                  HR('( %s ` 0 )' % IF, 'T', 'M', '( %s ` %s )' % (IF, NW), '( %s x. 1 )' % NW)))
    run = w.s([itr0, ant], 'mpd', '( %s -> %s )'
              % (ph, HR('( %s ` 0 )' % IF, 'T', 'M', '( %s ` %s )' % (IF, NW), '( %s x. 1 )' % NW)))
    # unfold the endpoints and the bound
    jvN = ifval(w, ph, NW, nwn2, w.s([u['tv'], u['dd'],
                w.s([u['kk'], prew(w, ph, NW, u['ww'], u['dkw'])], 'jca',
                    '( %s -> ( K e. %s /\\ %s e. Word %s ) )' % (ph, DG, PRE(NW), GK)),
                w.inst('tm2stkupd')], 'syl3anc',
                '( %s -> %s e. %s )' % (ph, UPD('T', 'D', 'K', PRE(NW)), STK('T'))))
    hc = w.s([nwn2], 'nn0cnd', '( %s -> %s e. CC )' % (ph, NW))
    m1 = w.s([hc, w.inst('mulrid')], 'syl', '( %s -> ( %s x. 1 ) = %s )' % (ph, NW, NW))
    q1 = w.s([jvN, m1], 'opeq12d', '( %s -> <. ( %s ` %s ) , ( %s x. 1 ) >. = <. %s , %s >. )'
             % (ph, IF, NW, NW, CLP(NW), NW))
    q2 = w.s([q1], 'breq2d', '( %s -> ( %s <-> %s ) )'
             % (ph, HR('( %s ` 0 )' % IF, 'T', 'M', '( %s ` %s )' % (IF, NW), '( %s x. 1 )' % NW),
                HR('( %s ` 0 )' % IF, 'T', 'M', CLP(NW), NW)))
    r1 = w.s([q2, run], 'mpbid', '( %s -> %s )'
             % (ph, HR('( %s ` 0 )' % IF, 'T', 'M', CLP(NW), NW)))
    q3 = w.s([jv0], 'breq1d', '( %s -> ( %s <-> %s ) )'
             % (ph, HR('( %s ` 0 )' % IF, 'T', 'M', CLP(NW), NW),
                HR(CLP('0'), 'T', 'M', CLP(NW), NW)))
    r2 = w.s([q3, r1], 'mpbid', '( %s -> %s )' % (ph, HR(CLP('0'), 'T', 'M', CLP(NW), NW)))
    # ( W prefix 0 ) = (/) and UPD( D , K , ( D ` K ) ) = D
    p00 = w.s([], 'pfx00', '( W prefix 0 ) = (/)')
    p00a = w.s([p00], 'a1i', '( %s -> ( W prefix 0 ) = (/) )' % ph)
    r0 = w.s([], 'rev0', '( reverse ` (/) ) = (/)')
    r0a = w.s([r0], 'a1i', '( %s -> ( reverse ` (/) ) = (/) )' % ph)
    lid = w.s([u['dkw'], w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ %s ) = %s )' % (ph, DK, DK))
    upi = w.s([u['tv'], u['dd'], u['kk'], w.inst('tm2stkupid')], 'syl3anc',
              '( %s -> %s = D )' % (ph, UPD('T', 'D', 'K', DK)))
    tbl = {'( W prefix 0 )': ('(/)', p00a), '( reverse ` (/) )': ('(/)', r0a),
           '( (/) ++ %s )' % DK: (DK, lid), UPD('T', 'D', 'K', DK): ('D', upi)}
    c0s, n0 = evaluate(w, ph, CLP('0'), {}, extra_rules=(lambda n: tbl.get(n.text())))
    TGT0 = '( { ( inl ` %s ) } X. ( %s X. { D } ) )' % (LB('0'), S('T'))
    assert n0 == TGT0, n0
    pid = w.s([u['ww'], w.inst('pfxid')], 'syl', '( %s -> ( W prefix %s ) = W )' % (ph, NW))
    tbl2 = {'( W prefix %s )' % NW: ('W', pid)}
    cNs, nN = evaluate(w, ph, CLP(NW), {}, extra_rules=(lambda n: tbl2.get(n.text())))
    TGTN = ('( { ( inl ` %s ) } X. ( %s X. { %s } ) )'
            % (LB(NW), S('T'), UPD('T', 'D', 'K', '( ( reverse ` W ) ++ %s )' % DK)))
    assert nN == TGTN, nN
    o2 = w.s([cNs], 'opeq1d', '( %s -> <. %s , %s >. = <. %s , %s >. )' % (ph, CLP(NW), NW, TGTN, NW))
    b4 = w.s([c0s, o2], 'breq12d', '( %s -> ( %s <-> %s ) )'
             % (ph, HR(CLP('0'), 'T', 'M', CLP(NW), NW), HR(TGT0, 'T', 'M', TGTN, NW)))
    w.qed([b4, r2], 'mpbid', '( %s -> %s )' % (ph, HR(TGT0, 'T', 'M', TGTN, NW)))
    return w.run()


if __name__ == '__main__':
    if want('tm2fpt'): tm2fpt()
