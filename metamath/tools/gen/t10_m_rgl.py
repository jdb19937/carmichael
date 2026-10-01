"""T10: small resGo facts for the resGoF loop.

  iptpos   ` 1 <_ ( isPrimeTD m ).2 ` (Lean ` isPrimeTD_cost_pos ` )
  rgln     ` # ( resGo z99 y q i ).1 <_ i ` and ` i <_ ( resGo z99 y q i ).2 ` (Lean ` resGo_length_le_fuel ` ,
           ` fuel_le_resGo_cost ` )

    MM_DB=sorties/t10.mm python3 tools/gen/t10_m_rgl.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t10lib import *
from lin import linarith, lineq
from cl import Closure
from t10_e_doa import P1, P2, snd_of, fst_of, ex_, lift_from
from t10_l_rga import RGX, KC, KEEPW, IPC, SMC, CST, STV, ST_RGSTEP, rgcl

SEL = sys.argv[1:]
ST_IPTPOS = '( M e. NN0 -> 1 <_ ( 2nd ` ( IsPrimeTD ` M ) ) )'
ST_RGLN = ('( ( ( G e. NN0 /\\ Y e. NN ) /\\ ( Q e. NN /\\ I e. NN0 ) ) -> ( ( # ` %s ) <_ I /\\ I <_ %s ) )'
           % (P1(RGX('Q', 'I')), P2(RGX('Q', 'I'))))


def iptpos():
    lab = 'iptpos'
    w = W(lab, 'Lean\'s ` isPrimeTD_cost_pos ` : the trial-division primality test charges at least once (~ isprimetdval ).')
    s = w.s
    ph = 'M e. NN0'
    PG = '( ( M PrimeGo 2 ) ` M )'
    IFV_ = 'if ( M < 2 , <. (/) , 1 >. , <. ( 1st ` %s ) , ( ( 2nd ` %s ) + 1 ) >. )' % (PG, PG)
    v = s([s([], 'id', '( M e. NN0 -> M e. NN0 )'), w.inst('isprimetdval')], 'syl', '( %s -> ( IsPrimeTD ` M ) = %s )' % (ph, IFV_)) if False else \
        s([], 'isprimetdval', '( %s -> ( IsPrimeTD ` M ) = %s )' % (ph, IFV_))
    outs = []
    for lt in (True, False):
        pc = '( %s /\\ %s )' % (ph, 'M < 2' if lt else '-. M < 2')
        cs = s([], 'simpr', '( %s -> %s )' % (pc, 'M < 2' if lt else '-. M < 2'))
        vv = s([v], 'adantr', '( %s -> ( IsPrimeTD ` M ) = %s )' % (pc, IFV_))
        if lt:
            e = s([vv, s([cs], 'iftrued', '( %s -> %s = <. (/) , 1 >. )' % (pc, IFV_))], 'eqtrd', '( %s -> ( IsPrimeTD ` M ) = <. (/) , 1 >. )' % pc)
            c2 = snd_of(w, pc, '( IsPrimeTD ` M )', '(/)', '1', e, ex_(w, pc, '(/)', '0ex') if False else s([s([], '0ex', '(/) e. _V')], 'a1i', '( %s -> (/) e. _V )' % pc),
                        s([s([], '1ex', '1 e. _V')], 'a1i', '( %s -> 1 e. _V )' % pc))
            le = s([c2, s([s([], '1re', '1 e. RR')], 'leidi' if False else 'lei' if False else 'a1i', '') if False else
                    s([s([s([], '1re', '1 e. RR')], 'leidi', '1 <_ 1')], 'a1i', '( %s -> 1 <_ 1 )' % pc)], 'breqtrrd', '( %s -> 1 <_ ( 2nd ` ( IsPrimeTD ` M ) ) )' % pc)
        else:
            X2 = '( ( 2nd ` %s ) + 1 )' % PG
            e = s([vv, s([cs], 'iffalsed', '( %s -> %s = <. ( 1st ` %s ) , %s >. )' % (pc, IFV_, PG, X2))], 'eqtrd',
                  '( %s -> ( IsPrimeTD ` M ) = <. ( 1st ` %s ) , %s >. )' % (pc, PG, X2))
            c2 = snd_of(w, pc, '( IsPrimeTD ` M )', '( 1st ` %s )' % PG, X2, e, ex_(w, pc, '( 1st ` %s )' % PG, 'fvex'), ex_(w, pc, X2, 'ovex'))
            mn = s([], 'simpl', '( %s -> M e. NN0 )' % pc)
            pgc = s([s([mn, closed(w, pc, '2nn0', '2 e. NN0')], 'jca', '( %s -> ( M e. NN0 /\\ 2 e. NN0 ) )' % pc), mn, w.inst('primegocl')], 'syl2anc',
                    '( %s -> %s e. ( 2o X. NN0 ) )' % (pc, PG))
            pn = s([pgc, w.inst('xp2nd')], 'syl', '( %s -> ( 2nd ` %s ) e. NN0 )' % (pc, PG))
            ge = s([s([pn, w.inst('nn0p1nn')], 'syl', '( %s -> %s e. NN )' % (pc, X2)), w.inst('nnge1')], 'syl', '( %s -> 1 <_ %s )' % (pc, X2))
            le = s([ge, c2], 'breqtrrd', '( %s -> 1 <_ ( 2nd ` ( IsPrimeTD ` M ) ) )' % pc)
        outs.append(le)
    w.qed(outs, 'pm2.61dan', ST_IPTPOS)
    return w.run()


def rgln():
    lab = 'rgln'
    w = W(lab, 'Lean\'s ` resGo_length_le_fuel ` and ` fuel_le_resGo_cost ` along the iterations: after ` i ` tests the kept list '
               'has at most ` i ` entries and at least ` i ` has been charged (~ rgstep ).')
    s = w.s
    ph = '( ( G e. NN0 /\\ Y e. NN ) /\\ Q e. NN )'
    PS = lambda n: '( ( # ` %s ) <_ %s /\\ %s <_ %s )' % (P1(RGX('Q', n)), n, n, P2(RGX('Q', n)))

    def sb(b):
        e = s([], 'id', '( n = %s -> n = %s )' % (b, b))
        st, new = w.wcongr(PS('n'), {'n': b}, 'n = %s' % b, {'n': e})
        assert new == PS(b), new
        return st
    hy = [sb('0'), sb('m'), sb('( m + 1 )'), sb('I')]
    g0 = s([s([], 'simpl', '( %s -> ( G e. NN0 /\\ Y e. NN ) )' % ph), s([], 'simpr', '( %s -> Q e. NN )' % ph)], 'jca', '( %s -> %s )' % (ph, ph)) if False else None
    r0 = s([], 'resgo0', '( %s -> %s = <. (/) , 0 >. )' % (ph, RGX('Q', '0')))
    ee = s([s([], '0ex', '(/) e. _V')], 'a1i', '( %s -> (/) e. _V )' % ph)
    ze = s([s([], 'c0ex', '0 e. _V')], 'a1i', '( %s -> 0 e. _V )' % ph)
    f1 = fst_of(w, ph, RGX('Q', '0'), '(/)', '0', r0, ee, ze)
    f2 = snd_of(w, ph, RGX('Q', '0'), '(/)', '0', r0, ee, ze)
    l0 = s([s([f1], 'fveq2d', '( %s -> ( # ` %s ) = ( # ` (/) ) )' % (ph, P1(RGX('Q', '0')))), s([s([], 'hash0', '( # ` (/) ) = 0')], 'a1i', '( %s -> ( # ` (/) ) = 0 )' % ph)],
           'eqtrd', '( %s -> ( # ` %s ) = 0 )' % (ph, P1(RGX('Q', '0'))))
    z00 = s([s([s([], '0re', '0 e. RR')], 'leidi', '0 <_ 0')], 'a1i', '( %s -> 0 <_ 0 )' % ph)
    b1 = s([l0, z00], 'eqbrtrd', '( %s -> ( # ` %s ) <_ 0 )' % (ph, P1(RGX('Q', '0'))))
    b2 = s([z00, f2], 'breqtrrd', '( %s -> 0 <_ %s )' % (ph, P2(RGX('Q', '0'))))
    base = s([b1, b2], 'jca', '( %s -> %s )' % (ph, PS('0')))
    a = '( ( %s /\\ m e. NN0 ) /\\ %s )' % (ph, PS('m'))
    mn = s([], 'simplr', '( %s -> m e. NN0 )' % a)
    ih = s([], 'simpr', '( %s -> %s )' % (a, PS('m')))
    gn = lift_from(w, ph, a, s([s([], 'simpl', '( %s -> ( G e. NN0 /\\ Y e. NN ) )' % ph)], 'simpld', '( %s -> G e. NN0 )' % ph))
    ynn = lift_from(w, ph, a, s([s([], 'simpl', '( %s -> ( G e. NN0 /\\ Y e. NN ) )' % ph)], 'simprd', '( %s -> Y e. NN )' % ph))
    qnn = lift_from(w, ph, a, s([], 'simpr', '( %s -> Q e. NN )' % ph))
    stp = s([s([s([gn, ynn], 'jca', '( %s -> ( G e. NN0 /\\ Y e. NN ) )' % a), s([qnn, mn], 'jca', '( %s -> ( Q e. NN /\\ m e. NN0 ) )' % a)], 'jca',
               '( %s -> ( ( G e. NN0 /\\ Y e. NN ) /\\ ( Q e. NN /\\ m e. NN0 ) ) )' % a), w.inst('rgstep')], 'syl',
            '( %s -> %s = %s )' % (a, RGX('Q', '( m + 1 )'), STV('Q', 'm')))
    L_, A_ = P1(RGX('Q', 'm')), P2(RGX('Q', 'm'))
    KW = KEEPW('( Q + m )')
    C_ = CST('( Q + m )')
    lw = s([rgcl(w, a, 'Q', 'm', gn, ynn, qnn, mn), w.inst('xp1st')], 'syl', '( %s -> %s e. Word NN0 )' % (a, L_))
    an = s([rgcl(w, a, 'Q', 'm', gn, ynn, qnn, mn), w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (a, A_))
    qm = '( Q + m )'
    qmn = s([qnn, mn, w.inst('nnnn0addcl')], 'syl2anc', '( %s -> %s e. NN )' % (a, qm))
    kww = s([s([s([qmn], 'nnnn0d', '( %s -> %s e. NN0 )' % (a, qm))], 's1cld', '( %s -> <" %s "> e. Word NN0 )' % (a, qm)),
             s([s([], 'wrd0', '(/) e. Word NN0')], 'a1i', '( %s -> (/) e. Word NN0 )' % a)], 'ifcld', '( %s -> %s e. Word NN0 )' % (a, KW))
    wex = ex_(w, a, '( %s ++ %s )' % (L_, KW), 'ovex')
    cex = ex_(w, a, '( %s + %s )' % (A_, C_), 'ovex')
    l1 = fst_of(w, a, RGX('Q', '( m + 1 )'), '( %s ++ %s )' % (L_, KW), '( %s + %s )' % (A_, C_), stp, wex, cex)
    a1 = snd_of(w, a, RGX('Q', '( m + 1 )'), '( %s ++ %s )' % (L_, KW), '( %s + %s )' % (A_, C_), stp, wex, cex)
    ln = s([s([l1], 'fveq2d', '( %s -> ( # ` %s ) = ( # ` ( %s ++ %s ) ) )' % (a, P1(RGX('Q', '( m + 1 )')), L_, KW)),
            s([lw, kww, w.inst('ccatlen')], 'syl2anc', '( %s -> ( # ` ( %s ++ %s ) ) = ( ( # ` %s ) + ( # ` %s ) ) )' % (a, L_, KW, L_, KW))], 'eqtrd',
           '( %s -> ( # ` %s ) = ( ( # ` %s ) + ( # ` %s ) ) )' % (a, P1(RGX('Q', '( m + 1 )')), L_, KW))
    # # KW <_ 1 by cases
    KCq = KC(qm)
    kc = []
    for tr in (True, False):
        pk = '( %s /\\ %s )' % (a, KCq if tr else '-. %s' % KCq)
        ck = s([], 'simpr', '( %s -> %s )' % (pk, KCq if tr else '-. %s' % KCq))
        if tr:
            e = s([s([ck], 'iftrued', '( %s -> %s = <" %s "> )' % (pk, KW, qm))], 'fveq2d', '( %s -> ( # ` %s ) = ( # ` <" %s "> ) )' % (pk, KW, qm))
            e = s([e, s([s([], 's1len', '( # ` <" %s "> ) = 1' % qm)], 'a1i', '( %s -> ( # ` <" %s "> ) = 1 )' % (pk, qm))], 'eqtrd',
                  '( %s -> ( # ` %s ) = 1 )' % (pk, KW))
            kc.append(s([e, s([s([s([], '1re', '1 e. RR')], 'leidi', '1 <_ 1')], 'a1i', '( %s -> 1 <_ 1 )' % pk)], 'eqbrtrd', '( %s -> ( # ` %s ) <_ 1 )' % (pk, KW)))
        else:
            e = s([s([ck], 'iffalsed', '( %s -> %s = (/) )' % (pk, KW))], 'fveq2d', '( %s -> ( # ` %s ) = ( # ` (/) ) )' % (pk, KW))
            e = s([e, s([s([], 'hash0', '( # ` (/) ) = 0')], 'a1i', '( %s -> ( # ` (/) ) = 0 )' % pk)], 'eqtrd', '( %s -> ( # ` %s ) = 0 )' % (pk, KW))
            kc.append(s([e, s([s([], '0le1', '0 <_ 1')], 'a1i', '( %s -> 0 <_ 1 )' % pk)], 'eqbrtrd', '( %s -> ( # ` %s ) <_ 1 )' % (pk, KW)))
    kle = s(kc, 'pm2.61dan', '( %s -> ( # ` %s ) <_ 1 )' % (a, KW))
    cl = Closure(w, a, {'m': ('NN0', mn)})
    cl.leaf('( # ` %s )' % L_, 'NN0', s([lw, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (a, L_)))
    cl.leaf('( # ` %s )' % KW, 'NN0', s([kww, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (a, KW)))
    cl.leaf('( # ` %s )' % P1(RGX('Q', '( m + 1 )')), 'NN0',
            s([s([rgcl(w, a, 'Q', '( m + 1 )', gn, ynn, qnn, s([mn, w.inst('peano2nn0')], 'syl', '( %s -> ( m + 1 ) e. NN0 )' % a)), w.inst('xp1st')],
                 'syl', '( %s -> %s e. Word NN0 )' % (a, P1(RGX('Q', '( m + 1 )')))), w.inst('lencl')], 'syl',
              '( %s -> ( # ` %s ) e. NN0 )' % (a, P1(RGX('Q', '( m + 1 )')))))
    ih1 = s([ih], 'simpld', '( %s -> ( # ` %s ) <_ m )' % (a, L_))
    ih2 = s([ih], 'simprd', '( %s -> m <_ %s )' % (a, A_))
    c1 = linarith(w, a, [ln, kle, ih1], '( # ` %s ) <_ ( m + 1 )' % P1(RGX('Q', '( m + 1 )')), closure=cl)
    ipn = s([s([s([qmn], 'nnnn0d', '( %s -> %s e. NN0 )' % (a, qm)), w.inst('isprimetdcl')], 'syl', '( %s -> ( IsPrimeTD ` %s ) e. ( 2o X. NN0 ) )' % (a, qm)),
             w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (a, IPC(qm)))
    smn = s([s([ynn, s([qmn, w.inst('nnm1nn0')], 'syl', '( %s -> ( %s - 1 ) e. NN0 )' % (a, qm)), w.inst('smoothtdcl')], 'syl2anc',
               '( %s -> ( Y SmoothTD ( %s - 1 ) ) e. ( 2o X. NN0 ) )' % (a, qm)), w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (a, SMC(qm)))
    for x_, st_ in ((A_, an), (IPC(qm), ipn), (SMC(qm), smn)):
        cl.leaf(x_, 'NN0', st_)
    A1 = P2(RGX('Q', '( m + 1 )'))
    cl.leaf(A1, 'NN0', s([rgcl(w, a, 'Q', '( m + 1 )', gn, ynn, qnn, s([mn, w.inst('peano2nn0')], 'syl', '( %s -> ( m + 1 ) e. NN0 )' % a)), w.inst('xp2nd')],
                         'syl', '( %s -> %s e. NN0 )' % (a, A1)))
    c2 = linarith(w, a, [a1, ih2, cl.ge0(IPC(qm)), cl.ge0(SMC(qm))], '( m + 1 ) <_ %s' % A1, closure=cl)
    st = s([c1, c2], 'jca', '( %s -> %s )' % (a, PS('( m + 1 )')))
    ind = s(hy + [base, st], 'nn0indd', '( ( %s /\\ I e. NN0 ) -> %s )' % (ph, PS('I')))
    p = '( ( G e. NN0 /\\ Y e. NN ) /\\ ( Q e. NN /\\ I e. NN0 ) )'
    w.qed([s([s([s([], 'simpl', '( %s -> ( G e. NN0 /\\ Y e. NN ) )' % p), s([], 'simprl', '( %s -> Q e. NN )' % p)], 'jca', '( %s -> %s )' % (p, ph)),
              s([], 'simprr', '( %s -> I e. NN0 )' % p)], 'jca', '( %s -> ( %s /\\ I e. NN0 ) )' % (p, ph)), ind], 'syl', ST_RGLN)
    return w.run()


EL = lambda i: '( ( encList ` ( reverse ` %s ) ) ++ R )' % P1(RGX('Q', i))
ST_RGENC = ('( ( ( ( G e. NN0 /\\ Y e. NN ) /\\ ( Q e. NN /\\ I e. NN0 ) ) /\\ R e. Word Gamma\' ) -> %s = if ( %s , %s , %s ) )'
            % (EL('( I + 1 )'), KC('( Q + I )'), EWg('( Q + I )', EL('I')), EL('I')))


def rgenc():
    lab = 'rgenc'
    w = W(lab, 'The open list of Lean\'s ` resGoF ` after one more test: its encoding (the kept numbers in reverse, above ` R ` ) '
               'gains ` q + i ` on top exactly when ` resKeep z99 y ( q + i ) ` (~ rgstep ).')
    s = w.s
    ph = '( ( ( G e. NN0 /\\ Y e. NN ) /\\ ( Q e. NN /\\ I e. NN0 ) ) /\\ R e. Word Gamma\' )'
    p0 = '( ( G e. NN0 /\\ Y e. NN ) /\\ ( Q e. NN /\\ I e. NN0 ) )'
    pp = s([], 'simpl', '( %s -> %s )' % (ph, p0))
    rw_ = s([], 'simpr', "( %s -> R e. Word Gamma' )" % ph)
    gn = s([s([pp], 'simpld', '( %s -> ( G e. NN0 /\\ Y e. NN ) )' % ph)], 'simpld', '( %s -> G e. NN0 )' % ph)
    ynn = s([s([pp], 'simpld', '( %s -> ( G e. NN0 /\\ Y e. NN ) )' % ph)], 'simprd', '( %s -> Y e. NN )' % ph)
    qnn = s([s([pp], 'simprd', '( %s -> ( Q e. NN /\\ I e. NN0 ) )' % ph)], 'simpld', '( %s -> Q e. NN )' % ph)
    inn = s([s([pp], 'simprd', '( %s -> ( Q e. NN /\\ I e. NN0 ) )' % ph)], 'simprd', '( %s -> I e. NN0 )' % ph)
    stp = s([pp, w.inst('rgstep')], 'syl', '( %s -> %s = %s )' % (ph, RGX('Q', '( I + 1 )'), STV('Q', 'I')))
    L_, A_ = P1(RGX('Q', 'I')), P2(RGX('Q', 'I'))
    q_ = '( Q + I )'
    KW = KEEPW(q_)
    lw = s([rgcl(w, ph, 'Q', 'I', gn, ynn, qnn, inn), w.inst('xp1st')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, L_))
    qn = s([s([qnn, inn, w.inst('nnnn0addcl')], 'syl2anc', '( %s -> %s e. NN )' % (ph, q_))], 'nnnn0d', '( %s -> %s e. NN0 )' % (ph, q_))
    kww = s([s([qn], 's1cld', '( %s -> <" %s "> e. Word NN0 )' % (ph, q_)), s([s([], 'wrd0', '(/) e. Word NN0')], 'a1i', '( %s -> (/) e. Word NN0 )' % ph)],
            'ifcld', '( %s -> %s e. Word NN0 )' % (ph, KW))
    l1 = fst_of(w, ph, RGX('Q', '( I + 1 )'), '( %s ++ %s )' % (L_, KW), '( %s + %s )' % (A_, CST(q_)), stp,
                ex_(w, ph, '( %s ++ %s )' % (L_, KW), 'ovex'), ex_(w, ph, '( %s + %s )' % (A_, CST(q_)), 'ovex'))
    rv = s([lw, kww, w.inst('revccat')], 'syl2anc', '( %s -> ( reverse ` ( %s ++ %s ) ) = ( ( reverse ` %s ) ++ ( reverse ` %s ) ) )' % (ph, L_, KW, KW, L_))
    RL = '( reverse ` %s )' % L_
    rlw = s([lw, w.inst('revcl')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, RL))
    e0 = s([s([s([l1], 'fveq2d', '( %s -> ( reverse ` %s ) = ( reverse ` ( %s ++ %s ) ) )' % (ph, P1(RGX('Q', '( I + 1 )')), L_, KW)), rv], 'eqtrd',
              '( %s -> ( reverse ` %s ) = ( ( reverse ` %s ) ++ %s ) )' % (ph, P1(RGX('Q', '( I + 1 )')), KW, RL))], 'fveq2d',
           '( %s -> ( encList ` ( reverse ` %s ) ) = ( encList ` ( ( reverse ` %s ) ++ %s ) ) )' % (ph, P1(RGX('Q', '( I + 1 )')), KW, RL))
    e1 = s([e0], 'oveq1d', '( %s -> %s = ( ( encList ` ( ( reverse ` %s ) ++ %s ) ) ++ R ) )' % (ph, EL('( I + 1 )'), KW, RL))
    KCq = KC(q_)
    IFV_ = 'if ( %s , %s , %s )' % (KCq, EWg(q_, EL('I')), EL('I'))
    outs = []
    for tr in (True, False):
        pk = '( %s /\\ %s )' % (ph, KCq if tr else '-. %s' % KCq)
        ck = s([], 'simpr', '( %s -> %s )' % (pk, KCq if tr else '-. %s' % KCq))
        L = lambda st: s([st], 'adantr', '( %s -> %s )' % (pk, concl(w, ph, st)))
        if tr:
            kq = s([ck], 'iftrued', '( %s -> %s = <" %s "> )' % (pk, KW, q_))
            rk = s([s([kq], 'fveq2d', '( %s -> ( reverse ` %s ) = ( reverse ` <" %s "> ) )' % (pk, KW, q_)),
                    s([s([], 'revs1', '( reverse ` <" %s "> ) = <" %s ">' % (q_, q_))], 'a1i', '( %s -> ( reverse ` <" %s "> ) = <" %s "> )' % (pk, q_, q_))],
                   'eqtrd', '( %s -> ( reverse ` %s ) = <" %s "> )' % (pk, KW, q_))
            W2 = '( <" %s "> ++ %s )' % (q_, RL)
            ec = s([L(qn), L(rlw), w.inst('tm2lenccons')], 'syl2anc', '( %s -> ( encList ` %s ) = ( ( encNatGam ` %s ) ++ ( <" 4 "> ++ ( encList ` %s ) ) ) )'
                   % (pk, W2, q_, RL))
            r1, x1 = w.rewrite('( ( encList ` ( ( reverse ` %s ) ++ %s ) ) ++ R )' % (KW, RL), {'( reverse ` %s )' % KW: ('<" %s ">' % q_, rk)}, pk)
            r2, x2 = w.rewrite(x1, {'( encList ` %s )' % W2: ('( ( encNatGam ` %s ) ++ ( <" 4 "> ++ ( encList ` %s ) ) )' % (q_, RL), ec)}, pk)
            en = s([L(rlw), w.inst('tm2lenccl')], 'syl', "( %s -> ( encList ` %s ) e. Word Gamma' )" % (pk, RL))
            eg = encw(w, pk, q_, L(qn))
            g4 = wg4(w, pk, '( encList ` %s )' % RL, en)
            s4 = s([closed(w, pk, 'gamma4', "4 e. Gamma'")], 's1cld', "( %s -> <\" 4 \"> e. Word Gamma' )" % pk)
            a1 = s([eg, g4, L(rw_), w.inst('ccatass')], 'syl3anc', '( %s -> %s = ( ( encNatGam ` %s ) ++ ( ( <" 4 "> ++ ( encList ` %s ) ) ++ R ) ) )'
                   % (pk, x2, q_, RL))
            a2 = s([s4, en, L(rw_), w.inst('ccatass')], 'syl3anc', '( %s -> ( ( <" 4 "> ++ ( encList ` %s ) ) ++ R ) = ( <" 4 "> ++ %s ) )' % (pk, RL, EL('I')))
            a3 = s([a2], 'oveq2d', '( %s -> ( ( encNatGam ` %s ) ++ ( ( <" 4 "> ++ ( encList ` %s ) ) ++ R ) ) = %s )' % (pk, q_, RL, EWg(q_, EL('I'))))
            v = s([s([s([s([r1, r2], 'eqtrd', '( %s -> ( ( encList ` ( ( reverse ` %s ) ++ %s ) ) ++ R ) = %s )' % (pk, KW, RL, x2)), a1], 'eqtrd',
                       '( %s -> ( ( encList ` ( ( reverse ` %s ) ++ %s ) ) ++ R ) = ( ( encNatGam ` %s ) ++ ( ( <" 4 "> ++ ( encList ` %s ) ) ++ R ) ) )'
                       % (pk, KW, RL, q_, RL)), a3], 'eqtrd', '( %s -> ( ( encList ` ( ( reverse ` %s ) ++ %s ) ) ++ R ) = %s )' % (pk, KW, RL, EWg(q_, EL('I')))),
                   s([s([ck], 'iftrued', '( %s -> %s = %s )' % (pk, IFV_, EWg(q_, EL('I'))))], 'eqcomd', '( %s -> %s = %s )' % (pk, EWg(q_, EL('I')), IFV_))],
                  'eqtrd', '( %s -> ( ( encList ` ( ( reverse ` %s ) ++ %s ) ) ++ R ) = %s )' % (pk, KW, RL, IFV_))
        else:
            kq = s([ck], 'iffalsed', '( %s -> %s = (/) )' % (pk, KW))
            rk = s([s([kq], 'fveq2d', '( %s -> ( reverse ` %s ) = ( reverse ` (/) ) )' % (pk, KW)),
                    s([s([], 'rev0', '( reverse ` (/) ) = (/)')], 'a1i', '( %s -> ( reverse ` (/) ) = (/) )' % pk)], 'eqtrd', '( %s -> ( reverse ` %s ) = (/) )' % (pk, KW))
            cid = s([L(rlw), w.inst('ccatrid')], 'syl', '( %s -> ( %s ++ (/) ) = %s )' % (pk, RL, RL))
            r1, x1 = w.rewrite('( ( encList ` ( ( reverse ` %s ) ++ %s ) ) ++ R )' % (KW, RL), {'( reverse ` %s )' % KW: ('(/)', rk)}, pk)
            cl0 = s([L(rlw), w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ %s ) = %s )' % (pk, RL, RL))
            r2, x2 = w.rewrite(x1, {'( (/) ++ %s )' % RL: (RL, cl0)}, pk)
            assert x2 == EL('I'), x2
            v = s([s([r1, r2], 'eqtrd', '( %s -> ( ( encList ` ( ( reverse ` %s ) ++ %s ) ) ++ R ) = %s )' % (pk, KW, RL, x2)),
                   s([s([ck], 'iffalsed', '( %s -> %s = %s )' % (pk, IFV_, EL('I')))], 'eqcomd', '( %s -> %s = %s )' % (pk, EL('I'), IFV_))], 'eqtrd',
                  '( %s -> ( ( encList ` ( ( reverse ` %s ) ++ %s ) ) ++ R ) = %s )' % (pk, KW, RL, IFV_))
        outs.append(v)
    c = s(outs, 'pm2.61dan', '( %s -> ( ( encList ` ( ( reverse ` %s ) ++ %s ) ) ++ R ) = %s )' % (ph, KW, RL, IFV_))
    w.qed([e1, c], 'eqtrd', ST_RGENC)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
