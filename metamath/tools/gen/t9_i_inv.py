"""T9: the size invariant of the extraction loop's state sequence (Lean ` extractFin_bounded ` along the recursion).

  tmextbb   equal tables are bounded alike
  exinvn    one step of the invariant when slot ` 1 mod L ` stays empty
  exinvs    one step of the invariant when it is filled (the table is reset)
  exinv     the invariant along the pool: some ` c <_ N + i ` bounds the table,
            ` m < 2 ^ ( bm + b ( N + i - c ) ) ` and ` # used + c <_ # used_0 + N + i `

    MM_DB=sorties/t9.mm python3 tools/gen/t9_i_inv.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t9lib import *
from lin import linarith, nlinarith, lineq
from t9_h_seq import (PH_S, SQW, ST_S0, ST_SP1, ST_SCL, ST_OPV, ST_OPCL, _cg)

SEL = sys.argv[1:]
ST_TBB = '( A = X -> ( %s <-> %s ) )' % (TBB('A', 'N'), TBB('X', 'N'))
ST_RALB = '( U = X -> ( %s <-> %s ) )' % (RALB('U'), RALB('X'))
T_I = ((('L e. NN', 'G e. NN0'), ('W e. Word NN0', 'Z e. %s' % STY)),
       (('N e. NN0', 'B e. NN0', 'C e. NN0'), RALB('W'), (TBB(ZA('Z'), 'N'), '%s < ( 2 ^ C )' % ZM('Z'))))
PH_I = cj(T_I)
Si = lambda t: '( %s ` %s )' % (SQW, t)


def BODY(t, c):
    return ('( %s /\\ %s < ( 2 ^ ( C + ( B x. ( ( N + %s ) - %s ) ) ) ) /\\ ( ( # ` %s ) + %s ) <_ ( ( # ` %s ) + ( N + %s ) ) )'
            % (TBB(ZA(Si(t)), c), ZM(Si(t)), t, c, ZU(Si(t)), c, ZU('Z'), t))


def INV(t):
    return 'E. c e. ( 0 ... ( N + %s ) ) %s' % (t, BODY(t, 'c'))


NW = '( # ` W )'
PM = '( W ` m )'
AM = ZA(Si('m'))
SLM = SLF('L', PM, AM)
T_C = ((T_I, 'm e. ( 0 ..^ %s )' % NW), ('e e. ( 0 ... ( N + m ) )', BODY('m', 'e')))
ST_N = '( ( %s /\\ %s = ( inr ` (/) ) ) -> %s )' % (cj(T_C), SLM, INV('( m + 1 )'))
ST_SS = '( ( %s /\\ %s =/= ( inr ` (/) ) ) -> %s )' % (cj(T_C), SLM, INV('( m + 1 )'))
ST_INV = '( ( %s /\\ I e. ( 0 ... %s ) ) -> %s )' % (PH_I, NW, INV('I'))


def tmextbb():
    lab = 'tmextbb'
    ph = 'A = X'
    w = W(lab, 'Equal tables are bounded alike (Lean ` TblBounded ` , TTAB\'s inlined form).')
    e = w.s([], 'id', '( A = X -> A = X )')
    st, new = w.wcongr(TBB('A', 'N'), {'A': 'X'}, ph, {'A': e})
    assert new == TBB('X', 'N'), new
    w.lines[-1] = 'qed:' + w.lines[-1].split(':', 1)[1] if w.lines[-1].split(':', 1)[0] == st else w.lines[-1]
    if not w.lines[-1].startswith('qed:'):
        qed_as(w, st, ST_TBB)
    return w.run()


def tmexralb():
    lab = 'tmexralb'
    ph = 'U = X'
    w = W(lab, 'Equal lists are bounded alike.')
    e = w.s([], 'id', '( U = X -> U = X )')
    st, new = w.wcongr(RALB('U'), {'U': 'X'}, ph, {'U': e})
    assert new == RALB('X'), new
    qed_as(w, st, ST_RALB)
    return w.run()


class Stp:
    """the facts of a step lemma under ph (the tree T_C plus the case)"""
    def __init__(self, w, ph, T):
        s = w.s
        self.w, self.ph = w, ph
        c = Ctx(w, ph, T)
        self.c = c
        self.ln, self.gn, self.ww, self.zs = c['L e. NN'], c['G e. NN0'], c['W e. Word NN0'], c['Z e. %s' % STY]
        self.nn, self.bn, self.cn = c['N e. NN0'], c['B e. NN0'], c['C e. NN0']
        mo = c['m e. ( 0 ..^ %s )' % NW]
        self.mz = s([mo, w.inst('elfzofz')], 'syl', '( %s -> m e. ( 0 ... %s ) )' % (ph, NW))
        self.mn = s([mo, w.inst('elfzonn0')], 'syl', '( %s -> m e. NN0 )' % ph)
        cz = c['e e. ( 0 ... ( N + m ) )']
        self.cc = s([cz, w.inst('elfznn0')], 'syl', '( %s -> e e. NN0 )' % ph)
        self.cle = s([cz, w.inst('elfzle2')], 'syl', '( %s -> e <_ ( N + m ) )' % ph)
        phs = s([c[PH_S] if PH_S in c.memo else None], 'id', '') if False else None
        self.phs = s([], 'id', '') if False else None
        psm = s([self.pS(), self.mz], 'jca', '( %s -> ( %s /\\ m e. ( 0 ... %s ) ) )' % (ph, PH_S, NW))
        self.sm = s([psm, w.inst('exstcl')], 'syl', '( %s -> %s e. %s )' % (ph, Si('m'), STY))
        self.pmn = s([self.ww, mo, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, PM))
        wr = s([s([self.ww, w.inst('wrdfn')], 'syl', '( %s -> W Fn ( 0 ..^ %s ) )' % (ph, NW)), mo, w.inst('fnfvelrn')], 'syl2anc',
               '( %s -> %s e. ran W )' % (ph, PM))
        self.pml = s([s([], 'breq1', '( a = %s -> ( a < ( 2 ^ B ) <-> %s < ( 2 ^ B ) ) )' % (PM, PM)), wr, c[RALB('W')]], 'rspcdva',
                     '( %s -> %s < ( 2 ^ B ) )' % (ph, PM))
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
        body = c[BODY('m', 'e')]
        self.tbm = s([body], 'simp1d', '( %s -> %s )' % (ph, TBB(AM, 'e')))
        self.mlt = s([body], 'simp2d', '( %s -> %s < ( 2 ^ ( C + ( B x. ( ( N + m ) - e ) ) ) ) )' % (ph, ZM(Si('m'))))
        self.len = s([body], 'simp3d', '( %s -> ( ( # ` %s ) + e ) <_ ( ( # ` %s ) + ( N + m ) ) )' % (ph, ZU(Si('m')), ZU('Z')))
        A1 = DP1('L', PM, AM)
        self.tb1 = s([s([s([self.ln, self.pmn, self.am], '3jca', '( %s -> ( L e. NN /\\ %s e. NN0 /\\ %s e. Tbl ) )' % (ph, PM, AM)),
                         s([self.cc, self.bn, self.pml], '3jca', '( %s -> ( e e. NN0 /\\ B e. NN0 /\\ %s < ( 2 ^ B ) ) )' % (ph, PM)),
                         self.tbm], '3jca', '( %s -> ( ( L e. NN /\\ %s e. NN0 /\\ %s e. Tbl ) /\\ ( e e. NN0 /\\ B e. NN0 /\\ %s < ( 2 ^ B ) ) /\\ %s ) )'
                         % (ph, PM, AM, PM, TBB(AM, 'e'))), w.inst('ttabtbdp')], 'syl', '( %s -> %s )' % (ph, TBB(A1, '( e + 1 )')))
        # the next state
        sp = s([s([self.pS(), self.mn], 'jca', '( %s -> ( %s /\\ m e. NN0 ) )' % (ph, PH_S)), w.inst('exstp1')], 'syl',
               '( %s -> %s = ( %s ( L ExStOp G ) %s ) )' % (ph, Si('( m + 1 )'), Si('m'), PM))
        ov = s([s([s([self.ln, self.gn], 'jca', '( %s -> ( L e. NN /\\ G e. NN0 ) )' % ph), s([sm, self.pmn], 'jca',
                  '( %s -> ( %s e. %s /\\ %s e. NN0 ) )' % (ph, Si('m'), STY, PM))], 'jca',
                  '( %s -> ( ( L e. NN /\\ G e. NN0 ) /\\ ( %s e. %s /\\ %s e. NN0 ) ) )' % (ph, Si('m'), STY, PM)), w.inst('exstopv')], 'syl',
               '( %s -> ( %s ( L ExStOp G ) %s ) = %s )' % (ph, Si('m'), PM, STOPB('L', 'G', Si('m'), PM)))
        self.nxt = s([sp, ov], 'eqtrd', '( %s -> %s = %s )' % (ph, Si('( m + 1 )'), STOPB('L', 'G', Si('m'), PM)))
        self.cl = Closure(w, ph, {'N': ('NN0', self.nn), 'B': ('NN0', self.bn), 'C': ('NN0', self.cn), 'm': ('NN0', self.mn),
                                  'e': ('NN0', self.cc)})
        self.cl.leaf('( # ` %s )' % ZU(Si('m')), 'NN0', s([self.um, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, ZU(Si('m')))))
        uz = s([s([self.zs, w.inst('xp2nd')], 'syl', '( %s -> ( 2nd ` Z ) e. %s )' % (ph, T23)), w.inst('xp1st')], 'syl',
               '( %s -> %s e. Word NN0 )' % (ph, ZU('Z')))
        self.cl.leaf('( # ` %s )' % ZU('Z'), 'NN0', s([uz, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, ZU('Z'))))

    def pS(self):
        w, ph, s, c = self.w, self.ph, self.w.s, self.c
        if not hasattr(self, '_ps'):
            self._ps = s([s([self.ln, self.gn], 'jca', '( %s -> ( L e. NN /\\ G e. NN0 ) )' % ph),
                          s([self.ww, self.zs], 'jca', '( %s -> ( W e. Word NN0 /\\ Z e. %s ) )' % (ph, STY))], 'jca', '( %s -> %s )' % (ph, PH_S))
        return self._ps

    def expo(self, e):
        """( ph -> ( 2 ^ e ) e. RR ) , e in NN0"""
        w, ph, s = self.w, self.ph, self.w.s
        return s([s([closed(w, ph, '2nn', '2 e. NN'), self.cl.mem(e, 'NN0'), w.inst('nnexpcl')], 'syl2anc', '( %s -> ( 2 ^ %s ) e. NN )' % (ph, e))],
                 'nnred', '( %s -> ( 2 ^ %s ) e. RR )' % (ph, e))

    def finish(self, zeq_parts, m_, u_, a_, cp, cpz, tbb_, mlt_, len_):
        """INV( m + 1 ) from the component facts about m_ u_ a_ (the next state's m used table) at the witness cp"""
        w, ph, s = self.w, self.ph, self.w.s
        S1 = Si('( m + 1 )')
        em, eu, ea = zeq_parts['m'], zeq_parts['u'], zeq_parts['a']
        # TBB and RALB through the helpers
        tb = s([s([ea], 'eqcomd', '( %s -> %s = %s )' % (ph, a_, ZA(S1)) if False else '( %s -> %s = %s )' % (ph, ZA(S1), a_)) if False else ea,
                w.inst('tmextbb')], 'syl', '( %s -> ( %s <-> %s ) )' % (ph, TBB(ZA(S1), cp), TBB(a_, cp)))
        tbb = s([tbb_, tb], 'mpbird', '( %s -> %s )' % (ph, TBB(ZA(S1), cp)))
        EXP = '( 2 ^ ( C + ( B x. ( ( N + ( m + 1 ) ) - %s ) ) ) )' % cp
        ml = s([s([em], 'breq1d', '( %s -> ( %s < %s <-> %s < %s ) )' % (ph, ZM(S1), EXP, m_, EXP)), mlt_], 'mpbird',
               '( %s -> %s < %s )' % (ph, ZM(S1), EXP))
        RHS = '( ( # ` %s ) + ( N + ( m + 1 ) ) )' % ZU('Z')
        le = s([s([s([s([eu], 'fveq2d', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (ph, ZU(S1), u_))], 'oveq1d',
                     '( %s -> ( ( # ` %s ) + %s ) = ( ( # ` %s ) + %s ) )' % (ph, ZU(S1), cp, u_, cp))], 'breq1d',
                  '( %s -> ( ( ( # ` %s ) + %s ) <_ %s <-> ( ( # ` %s ) + %s ) <_ %s ) )' % (ph, ZU(S1), cp, RHS, u_, cp, RHS)), len_], 'mpbird',
               '( %s -> ( ( # ` %s ) + %s ) <_ %s )' % (ph, ZU(S1), cp, RHS))
        bd = s([tbb, ml, le], '3jca', '( %s -> %s )' % (ph, BODY('( m + 1 )', cp)))
        e = s([], 'id', '( c = %s -> c = %s )' % (cp, cp))
        cg, new = w.wcongr(BODY('( m + 1 )', 'c'), {'c': cp}, 'c = %s' % cp, {'c': e})
        assert new == BODY('( m + 1 )', cp), new
        ex = s([cpz, bd, cg], 'rspcedvd' if False else 'id', '') if False else None
        ex = s([s([cpz, bd], 'jca', '( %s -> ( %s e. ( 0 ... ( N + ( m + 1 ) ) ) /\\ %s ) )' % (ph, cp, BODY('( m + 1 )', cp))),
                s([cg], 'rspcev', '( ( %s e. ( 0 ... ( N + ( m + 1 ) ) ) /\\ %s ) -> E. c e. ( 0 ... ( N + ( m + 1 ) ) ) %s )'
                  % (cp, BODY('( m + 1 )', cp), BODY('( m + 1 )', 'c')))], 'syl',
               '( %s -> E. c e. ( 0 ... ( N + ( m + 1 ) ) ) %s )' % (ph, BODY('( m + 1 )', 'c')))
        return ex


def exinvn():
    lab = 'exinvn'
    T = (T_C, '%s = ( inr ` (/) )' % SLM)
    ph = cj(T)
    w = W(lab, 'One step of the extraction invariant when the slot ` 1 mod L ` of the new table stays empty: the table grows by one '
               'entry per slot (~ ttabtbdp ), ` m ` and ` used ` stay.')
    s = w.s
    X = Stp(w, ph, T)
    c, cl = X.c, X.cl
    A1 = DP1('L', PM, AM)
    T1 = ZT(ZM(Si('m')), ZU(Si('m')), A1, '(/)')
    it = s([c['%s = ( inr ` (/) )' % SLM]], 'iftrued', '( %s -> %s = %s )' % (ph, STOPB('L', 'G', Si('m'), PM), T1))
    zeq = s([X.nxt, it], 'eqtrd', '( %s -> %s = %s )' % (ph, Si('( m + 1 )'), T1))
    vex = {'m': vex_(w, ph, ZM(Si('m'))), 'u': vex_(w, ph, ZU(Si('m'))), 'a': vex_(w, ph, A1), 'h': vex_(w, ph, '(/)')}
    zp = tup_comps(w, ph, Si('( m + 1 )'), zeq, ZM(Si('m')), ZU(Si('m')), A1, '(/)', vex)
    cp = '( e + 1 )'
    cpn = s([X.cc, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (ph, cp))
    cl.leaf(cp, 'NN0', cpn) if False else None
    cple = linarith(w, ph, [X.cle], '%s <_ ( N + ( m + 1 ) )' % cp, closure=cl)
    nm1 = cl.mem('( N + ( m + 1 ) )', 'NN0')
    cpz = s([s([cpn, nm1, cple], '3jca', '( %s -> ( %s e. NN0 /\\ ( N + ( m + 1 ) ) e. NN0 /\\ %s <_ ( N + ( m + 1 ) ) ) )' % (ph, cp, cp)),
             w.inst('elfz2nn0')], 'sylibr', '( %s -> %s e. ( 0 ... ( N + ( m + 1 ) ) ) )' % (ph, cp))
    E0 = '( C + ( B x. ( ( N + m ) - e ) ) )'
    E1 = '( C + ( B x. ( ( N + ( m + 1 ) ) - %s ) ) )' % cp
    ee = lineq(w, ph, E0, E1, closure=cl, products=True)
    mlt = s([X.mlt, s([ee], 'oveq2d', '( %s -> ( 2 ^ %s ) = ( 2 ^ %s ) )' % (ph, E0, E1))], 'breqtrd',
            '( %s -> %s < ( 2 ^ %s ) )' % (ph, ZM(Si('m')), E1))
    ln_ = linarith(w, ph, [X.len], '( ( # ` %s ) + %s ) <_ ( ( # ` %s ) + ( N + ( m + 1 ) ) )' % (ZU(Si('m')), cp, ZU('Z')), closure=cl)
    inv = X.finish(zp, ZM(Si('m')), ZU(Si('m')), A1, cp, cpz, X.tb1, mlt, ln_)
    qed_as(w, inv, ST_N)
    return w.run()


def exinvs():
    lab = 'exinvs'
    T = (T_C, '%s =/= ( inr ` (/) )' % SLM)
    ph = cj(T)
    w = W(lab, 'One step of the extraction invariant when the slot ` 1 mod L ` of the new table holds a witness ` S ` : ` m ` '
               'becomes ` m * prodL S ` with ` # S <_ c + 1 ` (~ ttabtbdp , ~ tplprodle ), ` used ` becomes ` S ++ used ` , '
               'the table is reset (~ ttabtbb0 ).')
    s = w.s
    X = Stp(w, ph, T)
    c, cl = X.c, X.cl
    A1 = DP1('L', PM, AM)
    WV = '( 2nd ` %s )' % SLM
    MM = '( %s x. %s )' % (ZM(Si('m')), PRL(WV))
    WU = '( %s ++ %s )' % (WV, ZU(Si('m')))
    HT = 'if ( G < %s , 1o , (/) )' % MM
    T2 = ZT(MM, WU, 'EmptyTbl', HT)
    nn = c['%s =/= ( inr ` (/) )' % SLM]
    it = s([s([nn], 'neneqd', '( %s -> -. %s = ( inr ` (/) ) )' % (ph, SLM))], 'iffalsed', '( %s -> %s = %s )' % (ph, STOPB('L', 'G', Si('m'), PM), T2))
    zeq = s([X.nxt, it], 'eqtrd', '( %s -> %s = %s )' % (ph, Si('( m + 1 )'), T2))
    hv = s([s([s([], '1oex', '1o e. _V'), s([], '0ex', '(/) e. _V')], 'ifex', '%s e. _V' % HT)], 'a1i', '( %s -> %s e. _V )' % (ph, HT))
    vex = {'m': vex_(w, ph, MM), 'u': vex_(w, ph, WU), 'a': vex_(w, ph, 'EmptyTbl'), 'h': hv}
    zp = tup_comps(w, ph, Si('( m + 1 )'), zeq, MM, WU, 'EmptyTbl', HT, vex)
    # the witness: # S <_ c + 1 , entries below 2 ^ b
    ML = '( 1 mod L )'
    mln = s([closed(w, ph, '1z', '1 e. ZZ'), X.ln, w.inst('zmodcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, ML))
    TBI = lambda d: '( ( %s ` %s ) =/= ( inr ` (/) ) -> ( ( # ` ( 2nd ` ( %s ` %s ) ) ) <_ ( e + 1 ) /\\ A. q e. ran ( 2nd ` ( %s ` %s ) ) q < ( 2 ^ B ) ) )' % (A1, d, A1, d, A1, d)
    idd = s([], 'id', '( d = %s -> d = %s )' % (ML, ML))
    cg, new = w.wcongr(TBI('d'), {'d': ML}, 'd = %s' % ML, {'d': idd})
    assert new == TBI(ML), new
    at = s([cg, mln, X.tb1], 'rspcdva', '( %s -> %s )' % (ph, TBI(ML)))
    both = s([nn, at], 'mpd', '( %s -> ( ( # ` %s ) <_ ( e + 1 ) /\\ A. q e. ran %s q < ( 2 ^ B ) ) )' % (ph, WV, WV))
    wl = s([both], 'simpld', '( %s -> ( # ` %s ) <_ ( e + 1 ) )' % (ph, WV))
    wq = s([both], 'simprd', '( %s -> A. q e. ran %s q < ( 2 ^ B ) )' % (ph, WV))
    wp = s([wq, s([s([], 'breq1', '( q = p -> ( q < ( 2 ^ B ) <-> p < ( 2 ^ B ) ) )')], 'cbvralvw',
                  '( A. q e. ran %s q < ( 2 ^ B ) <-> A. p e. ran %s p < ( 2 ^ B ) )' % (WV, WV))], 'sylib', '( %s -> A. p e. ran %s p < ( 2 ^ B ) )' % (ph, WV))
    wa = s([wq, s([s([], 'breq1', '( q = a -> ( q < ( 2 ^ B ) <-> a < ( 2 ^ B ) ) )')], 'cbvralvw',
                  '( A. q e. ran %s q < ( 2 ^ B ) <-> %s )' % (WV, RALB(WV)))], 'sylib', '( %s -> %s )' % (ph, RALB(WV)))
    sl = s([X.a1, mln, w.inst('tblfv')], 'syl2anc', '( %s -> %s e. ( Word NN0 |_| 1o ) )' % (ph, SLM))
    wvw = s([sl, w.inst('ttabopt')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, WV))
    pr = s([wvw, X.bn, wp, w.inst('tplprodle')], 'syl3anc', '( %s -> %s <_ ( 2 ^ ( ( # ` %s ) x. B ) ) )' % (ph, PRL(WV), WV))
    # m' < 2 ^ ( C + B ( N + m + 1 ) )
    LWV = '( # ` %s )' % WV
    cl.leaf(LWV, 'NN0', s([wvw, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, LWV)))
    E0 = '( C + ( B x. ( ( N + m ) - e ) ) )'
    EY = '( %s x. B )' % LWV
    E1 = '( C + ( B x. ( ( N + ( m + 1 ) ) - 0 ) ) )'
    prn = s([s([wvw, w.inst('prodlcl')], 'syl', '( %s -> ( ProdL ` %s ) e. ( NN0 X. NN0 ) )' % (ph, WV)), w.inst('xp1st')], 'syl',
            '( %s -> %s e. NN0 )' % (ph, PRL(WV)))
    cl.leaf(PRL(WV), 'NN0', prn)
    cl.leaf(ZM(Si('m')), 'NN0', X.mm)
    cmn = s([X.cle, w.inst('id')], 'id', '') if False else None
    e0n = s([s([s([X.cc, s([X.nn, X.mn], 'nn0addcld', '( %s -> ( N + m ) e. NN0 )' % ph), X.cle], '3jca',
                  '( %s -> ( c e. NN0 /\\ ( N + m ) e. NN0 /\\ c <_ ( N + m ) ) )' % ph), w.inst('elfz2nn0')], 'sylibr',
               '( %s -> c e. ( 0 ... ( N + m ) ) )' % ph)], 'id', '') if False else None
    dn = s([X.cc, s([X.nn, X.mn], 'nn0addcld', '( %s -> ( N + m ) e. NN0 )' % ph), X.cle, w.inst('nn0sub2')], 'syl3anc',
           '( %s -> ( ( N + m ) - e ) e. NN0 )' % ph)
    nm1n = cl.mem('( N + ( m + 1 ) )', 'NN0')
    s0e = s([s([nm1n], 'nn0cnd', '( %s -> ( N + ( m + 1 ) ) e. CC )' % ph)], 'subid1d', '( %s -> ( ( N + ( m + 1 ) ) - 0 ) = ( N + ( m + 1 ) ) )' % ph)
    s0n = s([s0e, nm1n], 'eqeltrd', '( %s -> ( ( N + ( m + 1 ) ) - 0 ) e. NN0 )' % ph)
    E0n = s([X.cn, s([X.bn, dn], 'nn0mulcld', '( %s -> ( B x. ( ( N + m ) - e ) ) e. NN0 )' % ph)], 'nn0addcld', '( %s -> %s e. NN0 )' % (ph, E0))
    cl.leaf(E0, 'NN0', E0n) if False else None
    two = closed(w, ph, '2cn', '2 e. CC')
    eyn = s([cl.mem(LWV, 'NN0'), X.bn], 'nn0mulcld', '( %s -> %s e. NN0 )' % (ph, EY))
    p0 = s([s([closed(w, ph, '2nn', '2 e. NN'), E0n, w.inst('nnexpcl')], 'syl2anc', '( %s -> ( 2 ^ %s ) e. NN )' % (ph, E0))], 'nnred',
           '( %s -> ( 2 ^ %s ) e. RR )' % (ph, E0))
    py = s([s([closed(w, ph, '2nn', '2 e. NN'), eyn, w.inst('nnexpcl')], 'syl2anc', '( %s -> ( 2 ^ %s ) e. NN )' % (ph, EY))], 'nnred',
           '( %s -> ( 2 ^ %s ) e. RR )' % (ph, EY))
    pyp = s([s([closed(w, ph, '2nn', '2 e. NN'), eyn, w.inst('nnexpcl')], 'syl2anc', '( %s -> ( 2 ^ %s ) e. NN )' % (ph, EY))], 'nngt0d',
            '( %s -> 0 < ( 2 ^ %s ) )' % (ph, EY))
    mr = s([X.mm], 'nn0red', '( %s -> %s e. RR )' % (ph, ZM(Si('m'))))
    prr = s([prn], 'nn0red', '( %s -> %s e. RR )' % (ph, PRL(WV)))
    l1 = s([prr, py, mr, s([X.mm], 'nn0ge0d', '( %s -> 0 <_ %s )' % (ph, ZM(Si('m')))), pr], 'lemul2ad',
           '( %s -> ( %s x. %s ) <_ ( %s x. ( 2 ^ %s ) ) )' % (ph, ZM(Si('m')), PRL(WV), ZM(Si('m')), EY))
    l2 = s([s([mr, p0, py, pyp], 'ltmul1d' if False else 'id', '') if False else None], 'id', '') if False else None
    pyrp = s([s([closed(w, ph, '2nn', '2 e. NN'), eyn, w.inst('nnexpcl')], 'syl2anc', '( %s -> ( 2 ^ %s ) e. NN )' % (ph, EY))], 'nnrpd',
             '( %s -> ( 2 ^ %s ) e. RR+ )' % (ph, EY))
    lm = s([mr, p0, pyrp], 'ltmul1d', '( %s -> ( %s < ( 2 ^ %s ) <-> ( %s x. ( 2 ^ %s ) ) < ( ( 2 ^ %s ) x. ( 2 ^ %s ) ) ) )'
           % (ph, ZM(Si('m')), E0, ZM(Si('m')), EY, E0, EY))
    l2 = s([X.mlt, lm], 'mpbid', '( %s -> ( %s x. ( 2 ^ %s ) ) < ( ( 2 ^ %s ) x. ( 2 ^ %s ) ) )' % (ph, ZM(Si('m')), EY, E0, EY))
    ea = s([two, E0n, eyn, w.inst('expadd')], 'syl3anc', '( %s -> ( 2 ^ ( %s + %s ) ) = ( ( 2 ^ %s ) x. ( 2 ^ %s ) ) )' % (ph, E0, EY, E0, EY))
    # exponent bound: E0 + EY <_ E1
    bw = s([cl.mem(LWV, 'RR'), cl.mem('( e + 1 )', 'RR'), cl.mem('B', 'RR'), cl.ge0('B'), wl], 'lemul1ad',
           '( %s -> ( %s x. B ) <_ ( ( e + 1 ) x. B ) )' % (ph, LWV))
    cl.leaf(E0, 'NN0', E0n) if False else None
    dle = linarith(w, ph, [bw, X.cle], '( %s + %s ) <_ %s' % (E0, EY, E1), closure=cl, products=True)
    e1n = s([X.cn, s([X.bn, s0n], 'nn0mulcld', '( %s -> ( B x. ( ( N + ( m + 1 ) ) - 0 ) ) e. NN0 )' % ph)], 'nn0addcld', '( %s -> %s e. NN0 )' % (ph, E1))
    e0y = s([s([E0n, eyn], 'nn0addcld', '( %s -> ( %s + %s ) e. NN0 )' % (ph, E0, EY))], 'nn0zd', '( %s -> ( %s + %s ) e. ZZ )' % (ph, E0, EY))
    ez = s([e0y, s([e1n], 'nn0zd', '( %s -> %s e. ZZ )' % (ph, E1)), dle], '3jca', '( %s -> ( ( %s + %s ) e. ZZ /\\ %s e. ZZ /\\ ( %s + %s ) <_ %s ) )'
           % (ph, E0, EY, E1, E0, EY, E1))
    eu = s([ez, w.inst('eluz2')], 'sylibr', '( %s -> %s e. ( ZZ>= ` ( %s + %s ) ) )' % (ph, E1, E0, EY))
    pe = s([closed(w, ph, '2re', '2 e. RR'), closed(w, ph, '1le2', '1 <_ 2'), eu, w.inst('leexp2a')], 'syl3anc',
           '( %s -> ( 2 ^ ( %s + %s ) ) <_ ( 2 ^ %s ) )' % (ph, E0, EY, E1))
    RA = '( ( 2 ^ %s ) x. ( 2 ^ %s ) )' % (E0, EY)
    rr_ = s([p0, py], 'remulcld', '( %s -> %s e. RR )' % (ph, RA))
    pe2 = s([ea, pe], 'eqbrtrrd', '( %s -> %s <_ ( 2 ^ %s ) )' % (ph, RA, E1))
    p1 = s([s([closed(w, ph, '2nn', '2 e. NN'), e1n, w.inst('nnexpcl')], 'syl2anc', '( %s -> ( 2 ^ %s ) e. NN )' % (ph, E1))], 'nnred',
           '( %s -> ( 2 ^ %s ) e. RR )' % (ph, E1))
    mpr = s([mr, prr], 'remulcld', '( %s -> %s e. RR )' % (ph, MM))
    mpy = s([mr, py], 'remulcld', '( %s -> ( %s x. ( 2 ^ %s ) ) e. RR )' % (ph, ZM(Si('m')), EY))
    t1 = s([mpr, mpy, rr_, l1, l2], 'lelttrd', '( %s -> %s < %s )' % (ph, MM, RA))
    mlt = s([mpr, rr_, p1, t1, pe2], 'ltletrd', '( %s -> %s < ( 2 ^ %s ) )' % (ph, MM, E1))
    # witness 0
    z0 = s([s([closed(w, ph, '0nn0', '0 e. NN0'), cl.mem('( N + ( m + 1 ) )', 'NN0'), cl.ge0('( N + ( m + 1 ) )')], '3jca',
              '( %s -> ( 0 e. NN0 /\\ ( N + ( m + 1 ) ) e. NN0 /\\ 0 <_ ( N + ( m + 1 ) ) ) )' % ph), w.inst('elfz2nn0')], 'sylibr',
           '( %s -> 0 e. ( 0 ... ( N + ( m + 1 ) ) ) )' % ph)
    tb0 = s([closed(w, ph, '0nn0', '0 e. NN0'), X.bn, w.inst('ttabtbb0')], 'syl2anc', '( %s -> %s )' % (ph, TBB('EmptyTbl', '0')))
    # used: entries and length
    lw_ = s([wvw, X.um, w.inst('ccatlen')], 'syl2anc', '( %s -> ( # ` %s ) = ( ( # ` %s ) + ( # ` %s ) ) )' % (ph, WU, WV, ZU(Si('m'))))
    cl.leaf('( # ` %s )' % WU, 'NN0', s([s([wvw, X.um, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word NN0 )' % (ph, WU)), w.inst('lencl')], 'syl',
                                        '( %s -> ( # ` %s ) e. NN0 )' % (ph, WU)))
    ln_ = linarith(w, ph, [lw_, wl, X.len], '( ( # ` %s ) + 0 ) <_ ( ( # ` %s ) + ( N + ( m + 1 ) ) )' % (WU, ZU('Z')), closure=cl)
    inv = X.finish(zp, MM, WU, 'EmptyTbl', '0', z0, tb0, mlt, ln_)
    qed_as(w, inv, ST_SS)
    return w.run()



def exinv():
    lab = 'exinv'
    ph = PH_I
    w = W(lab, 'The size invariant of the extraction loop along the pool (Lean ` extractFin_bounded ` \'s induction): '
               'some ` c <_ N + i ` bounds the table\'s witnesses, ` m < 2 ^ ( bm + b ( N + i - c ) ) ` '
               'and ` # used + c <_ # used_0 + N + i ` (~ exinvn , ~ exinvs ).')
    s = w.s
    c = Ctx(w, ph, T_I)
    ps0 = s([s([c['L e. NN'], c['G e. NN0']], 'jca', '( %s -> ( L e. NN /\\ G e. NN0 ) )' % ph),
             s([c['W e. Word NN0'], c['Z e. %s' % STY]], 'jca', '( %s -> ( W e. Word NN0 /\\ Z e. %s ) )' % (ph, STY))], 'jca',
            '( %s -> %s )' % (ph, PH_S))
    PS = lambda t: '( %s <_ %s -> %s )' % (t, NW, INV(t))
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
    t0 = s([c[TBB(ZA('Z'), 'N')], s([ea, w.inst('tmextbb')], 'syl', '( %s -> ( %s <-> %s ) )' % (ph, TBB(ZA(S0), 'N'), TBB(ZA('Z'), 'N')))], 'mpbird',
           '( %s -> %s )' % (ph, TBB(ZA(S0), 'N')))
    nn, bn, cn = c['N e. NN0'], c['B e. NN0'], c['C e. NN0']
    cl = Closure(w, ph, {'N': ('NN0', nn), 'B': ('NN0', bn), 'C': ('NN0', cn)})
    E00 = '( C + ( B x. ( ( N + 0 ) - N ) ) )'
    ee = lineq(w, ph, E00, 'C', closure=cl, products=True)
    ml = s([s([em, s([ee], 'oveq2d', '( %s -> ( 2 ^ %s ) = ( 2 ^ C ) )' % (ph, E00))], 'breq12d',
              '( %s -> ( %s < ( 2 ^ %s ) <-> %s < ( 2 ^ C ) ) )' % (ph, ZM(S0), E00, ZM('Z'))), c['%s < ( 2 ^ C )' % ZM('Z')]], 'mpbird',
           '( %s -> %s < ( 2 ^ %s ) )' % (ph, ZM(S0), E00))
    uz = s([s([c['Z e. %s' % STY], w.inst('xp2nd')], 'syl', '( %s -> ( 2nd ` Z ) e. ( Word NN0 X. ( Tbl X. 2o ) ) )' % ph), w.inst('xp1st')], 'syl',
           '( %s -> %s e. Word NN0 )' % (ph, ZU('Z')))
    cl.leaf('( # ` %s )' % ZU('Z'), 'NN0', s([uz, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, ZU('Z'))))
    lu = s([eu], 'fveq2d', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (ph, ZU(S0), ZU('Z')))
    cl.leaf('( # ` %s )' % ZU(S0), 'NN0', s([lu, cl.mem('( # ` %s )' % ZU('Z'), 'NN0')], 'eqeltrd', '( %s -> ( # ` %s ) e. NN0 )' % (ph, ZU(S0))))
    ln0 = linarith(w, ph, [lu], '( ( # ` %s ) + N ) <_ ( ( # ` %s ) + ( N + 0 ) )' % (ZU(S0), ZU('Z')), closure=cl)
    bd = s([t0, ml, ln0], '3jca', '( %s -> %s )' % (ph, BODY('0', 'N')))
    nz = s([s([nn, cl.mem('( N + 0 )', 'NN0'), linarith(w, ph, [], 'N <_ ( N + 0 )', closure=cl)], '3jca',
              '( %s -> ( N e. NN0 /\\ ( N + 0 ) e. NN0 /\\ N <_ ( N + 0 ) ) )' % ph), w.inst('elfz2nn0')], 'sylibr', '( %s -> N e. ( 0 ... ( N + 0 ) ) )' % ph)
    e_ = s([], 'id', '( c = N -> c = N )')
    cg, new = w.wcongr(BODY('0', 'c'), {'c': 'N'}, 'c = N', {'c': e_})
    assert new == BODY('0', 'N'), new
    ex0 = s([s([nz, bd], 'jca', '( %s -> ( N e. ( 0 ... ( N + 0 ) ) /\\ %s ) )' % (ph, BODY('0', 'N'))),
             s([cg], 'rspcev', '( ( N e. ( 0 ... ( N + 0 ) ) /\\ %s ) -> E. c e. ( 0 ... ( N + 0 ) ) %s )' % (BODY('0', 'N'), BODY('0', 'c')))], 'syl',
            '( %s -> E. c e. ( 0 ... ( N + 0 ) ) %s )' % (ph, BODY('0', 'c')))
    base = s([ex0], 'a1d', '( %s -> %s )' % (ph, PS('0')))
    # step
    a = '( ( %s /\\ m e. NN0 ) /\\ %s )' % (ph, PS('m'))
    a2 = '( %s /\\ ( m + 1 ) <_ %s )' % (a, NW)
    La = lambda st: s([s([s([st], 'adantr', '( ( %s /\\ m e. NN0 ) -> %s )' % (ph, concl(w, ph, st)))], 'adantr', '( %s -> %s )' % (a, concl(w, ph, st)))],
                      'adantr', '( %s -> %s )' % (a2, concl(w, ph, st)))
    mn = s([s([], 'simplr', '( %s -> m e. NN0 )' % a)], 'adantr', '( %s -> m e. NN0 )' % a2)
    ih0 = s([s([], 'simpr', '( %s -> %s )' % (a, PS('m')))], 'adantr', '( %s -> %s )' % (a2, PS('m')))
    m1l = s([], 'simpr', '( %s -> ( m + 1 ) <_ %s )' % (a2, NW))
    lw = s([La(c['W e. Word NN0']), w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (a2, NW))
    cla = Closure(w, a2, {'m': ('NN0', mn), NW: ('NN0', lw)})
    mle = linarith(w, a2, [m1l], 'm <_ %s' % NW, closure=cla)
    ih = s([mle, ih0], 'mpd', '( %s -> %s )' % (a2, INV('m')))
    mlt = linarith(w, a2, [m1l], 'm < %s' % NW, closure=cla)
    posw = linarith(w, a2, [m1l, cla.ge0('m')], '0 < %s' % NW, closure=cla)
    wnn = s([s([lw, posw], 'jca', '( %s -> ( %s e. NN0 /\\ 0 < %s ) )' % (a2, NW, NW)), w.inst('elnnnn0b')], 'sylibr', '( %s -> %s e. NN )' % (a2, NW))
    mo = s([s([mn, wnn, mlt], '3jca', '( %s -> ( m e. NN0 /\\ %s e. NN /\\ m < %s ) )' % (a2, NW, NW)), w.inst('elfzo0')], 'sylibr',
           '( %s -> m e. ( 0 ..^ %s ) )' % (a2, NW))
    exm = ih
    e2 = s([], 'id', '( c = e -> c = e )')
    cg2, new2 = w.wcongr(BODY('m', 'c'), {'c': 'e'}, 'c = e', {'c': e2})
    cbv = s([cg2], 'cbvrexvw', '( E. c e. ( 0 ... ( N + m ) ) %s <-> E. e e. ( 0 ... ( N + m ) ) %s )' % (BODY('m', 'c'), BODY('m', 'e')))
    exe = s([exm, cbv], 'sylib', '( %s -> E. e e. ( 0 ... ( N + m ) ) %s )' % (a2, BODY('m', 'e')))
    ae = '( %s /\\ ( e e. ( 0 ... ( N + m ) ) /\\ %s ) )' % (a2, BODY('m', 'e'))
    Le = lambda st: s([st], 'adantr', '( %s -> %s )' % (ae, concl(w, a2, st)))
    ez = s([], 'simprl', '( %s -> e e. ( 0 ... ( N + m ) ) )' % ae)
    eb = s([], 'simprr', '( %s -> %s )' % (ae, BODY('m', 'e')))
    phm = s([s([s([s([], 'simpl', '( ( %s /\\ m e. NN0 ) -> %s )' % (ph, ph))], 'adantr', '( %s -> %s )' % (a, ph))], 'adantr', '( %s -> %s )' % (a2, ph))],
            'adantr', '( %s -> %s )' % (ae, ph))
    tc = s([s([phm, Le(mo)], 'jca', '( %s -> ( %s /\\ m e. ( 0 ..^ %s ) ) )' % (ae, ph, NW)),
            s([ez, eb], 'jca', '( %s -> ( e e. ( 0 ... ( N + m ) ) /\\ %s ) )' % (ae, BODY('m', 'e')))], 'jca',
           '( %s -> %s )' % (ae, cj(T_C)))
    cn_ = s([s([], 'exinvn', ST_N)], 'ex', '( %s -> ( %s = ( inr ` (/) ) -> %s ) )' % (cj(T_C), SLM, INV('( m + 1 )')))
    cs_ = s([s([], 'exinvs', ST_SS)], 'ex', '( %s -> ( %s =/= ( inr ` (/) ) -> %s ) )' % (cj(T_C), SLM, INV('( m + 1 )')))
    cases = s([cn_, cs_], 'pm2.61dne', '( %s -> %s )' % (cj(T_C), INV('( m + 1 )')))
    q1 = s([tc, cases], 'syl', '( %s -> %s )' % (ae, INV('( m + 1 )')))
    lim = s([q1], 'rexlimdvaa', '( %s -> ( E. e e. ( 0 ... ( N + m ) ) %s -> %s ) )' % (a2, BODY('m', 'e'), INV('( m + 1 )')))
    q2 = s([exe, lim], 'mpd', '( %s -> %s )' % (a2, INV('( m + 1 )')))
    st = s([q2], 'ex', '( %s -> %s )' % (a, PS('( m + 1 )')))
    ind = s([h1, h2, h3, h4, base, st], 'nn0indd', '( ( %s /\\ I e. NN0 ) -> %s )' % (ph, PS('I')))
    p = '( %s /\\ I e. ( 0 ... %s ) )' % (ph, NW)
    ifz = s([], 'simpr', '( %s -> I e. ( 0 ... %s ) )' % (p, NW))
    inn = s([ifz, w.inst('elfznn0')], 'syl', '( %s -> I e. NN0 )' % p)
    ile = s([ifz, w.inst('elfzle2')], 'syl', '( %s -> I <_ %s )' % (p, NW))
    i2 = s([s([s([], 'simpl', '( %s -> %s )' % (p, ph)), inn], 'jca', '( %s -> ( %s /\\ I e. NN0 ) )' % (p, ph)), ind], 'syl', '( %s -> %s )' % (p, PS('I')))
    w.qed([ile, i2], 'mpd', ST_INV)
    return w.run()


STMTS = {'tmextbb': ST_TBB, 'exinvn': ST_N, 'exinvs': ST_SS, 'exinv': ST_INV}

if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
