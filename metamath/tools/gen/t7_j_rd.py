"""T7: the read phase of the two-operand loops at the machine, one operand at a
time: ` branch da ( pop K readA ) ` at iteration ` N ` (Lean ` OpA.read ` ) and
the same for ` readB ` , as the if-term of T5's ` tm2fadrd ` interface."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t7lib import *
from cl import Closure

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

LN = '( # ` L )'
UB = lambda t: 'if ( %s < %s , <. 1 , ( L ` %s ) >. , 4 )' % (t, LN, t)
R = OPR('L')
SIDE = {'A': dict(reg='ra', flag='da', others=['car', 'rb', 'db', 'cmp'], F='TMrdA', ST=ST_RDA, PH=PH_RDA, n1=RD1),
        'B': dict(reg='rb', flag='db', others=['car', 'ra', 'da', 'cmp'], F='TMrdB', ST=ST_RDB, PH=PH_RDB, n1=RD2)}


def tmcrd(h):
    sd = SIDE[h]
    lab = 'tmcrd%s' % h.lower()
    ph = sd['PH']
    n1 = sd['n1']
    REG, FLAG = ACC[sd['reg']], ACC[sd['flag']]
    G = sd['ST'][len('( %s -> ' % ph):-2]
    w = W(lab, ('The read phase of operand %s of a two-operand loop at iteration ` N ` (Lean ` Op%s.read ` ): '
                '` branch d%s ( pop K read%s ) ` pops the ` N ` -th bit letter or the terminator while ` N <_ ( # ` L ) ` '
                'and does nothing afterwards; the flag becomes ` [ ( # ` L ) <_ N ] ` , the register the bit or ` none ` , '
                'the other fields stay.') % ({'A': '` a `', 'B': '` b `'}[h], h, h.lower(), h))
    ll = w.s([], 'simpll', '( %s -> L e. Word 2o )' % ph)
    nn = w.s([], 'simplr', '( %s -> N e. NN0 )' % ph)
    vv = w.s([], 'simpr1', '( %s -> V e. TMSt )' % ph)
    vfl = w.s([], 'simpr2', '( %s -> ( %s ` V ) = %s )' % (ph, FLAG, FLG('L', '<', 'N')))
    vrg = w.s([], 'simpr3', '( %s -> ( %s < N -> ( %s ` V ) = ( inr ` (/) ) ) )' % (ph, LN, REG))
    ln = w.s([ll, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, LN))
    UF = OPU('L')
    NU = '( %s ` <. V , ( inl ` ( %s ` N ) ) >. )' % (sd['F'], UF)

    def finish(pc, mem, fl, rg, oth):
        a = w.s([fl, rg], 'jca', '( %s -> ( ( %s ` %s ) = %s /\\ ( %s ` %s ) = %s ) )' % (pc, FLAG, n1, FLG('L', '<_', 'N'), REG, n1, RGV('L', 'N')))
        o = sd['others']
        f = lambda k: '( %s ` %s ) = ( %s ` V )' % (ACC[k], n1, ACC[k])
        b1 = w.s([oth[o[0]], oth[o[1]]], 'jca', '( %s -> ( %s /\\ %s ) )' % (pc, f(o[0]), f(o[1])))
        b2 = w.s([oth[o[2]], oth[o[3]]], 'jca', '( %s -> ( %s /\\ %s ) )' % (pc, f(o[2]), f(o[3])))
        b = w.s([b1, b2], 'jca', '( %s -> ( ( %s /\\ %s ) /\\ ( %s /\\ %s ) ) )' % (pc, f(o[0]), f(o[1]), f(o[2]), f(o[3])))
        return w.s([mem, a, b], '3jca', '( %s -> %s )' % (pc, G))

    def lift(pc, st, f):
        return w.s([st], 'adantr', '( %s -> %s )' % (pc, f))

    def readcase(pc, Z, zstep, nv, inR):
        """n1 = NU = NZ ; returns (mem, field steps of n1)"""
        it = w.s([inR], 'iftrued', '( %s -> %s = %s )' % (pc, n1, NU))
        NZ = NVF(sd['F'], 'V', Z)
        e1 = w.s([zstep], 'fveq2d', '( %s -> ( inl ` ( %s ` N ) ) = ( inl ` %s ) )' % (pc, UF, Z))
        e2 = w.s([e1], 'opeq2d', '( %s -> <. V , ( inl ` ( %s ` N ) ) >. = <. V , ( inl ` %s ) >. )' % (pc, UF, Z))
        e3 = w.s([e2], 'fveq2d', '( %s -> %s = %s )' % (pc, NU, NZ))
        eq = w.s([it, e3], 'eqtrd', '( %s -> %s = %s )' % (pc, n1, NZ))
        mem = w.s([eq, nv['mem']], 'eqeltrd', '( %s -> %s e. TMSt )' % (pc, n1))
        flds = {}
        for f in ORDER:
            g = w.s([eq], 'fveq2d', '( %s -> ( %s ` %s ) = ( %s ` %s ) )' % (pc, ACC[f], n1, ACC[f], NZ))
            flds[f] = w.s([g, nv['fields'][f]], 'eqtrd', '( %s -> ( %s ` %s ) = %s )' % (pc, ACC[f], n1, nv['comps'][ORDER.index(f)]))
        return mem, flds

    def uvalue(pc, nnc, llc, target, cond_true, cond_step):
        """( pc -> ( OPU ` N ) = target )"""
        z_bit = '<. 1 , ( L ` N ) >.'
        # typing of the if-term (for the value's set-hood): ifex from opex and 4
        o1 = w.s([], 'opex', '%s e. _V' % z_bit)
        f4 = w.s([w.s([], '4re', '4 e. RR')], 'elexi', '4 e. _V')
        ie = w.s([o1, f4], 'ifex', '%s e. _V' % UB('N'))
        iea = w.s([ie], 'a1i', '( %s -> %s e. _V )' % (pc, UB('N')))
        v = mval(w, pc, 'j', 'NN0', UB, 'N', nnc, iea, force_g=True)
        it = w.s([cond_step], 'iftrued' if cond_true else 'iffalsed', '( %s -> %s = %s )' % (pc, UB('N'), target))
        return w.s([v, it], 'eqtrd', '( %s -> ( %s ` N ) = %s )' % (pc, UF, target))

    # ---------------- case N < |L|
    pa = '( %s /\\ N < %s )' % (ph, LN)
    lt = w.s([], 'simpr', '( %s -> N < %s )' % (pa, LN))
    lla, nna, vva, lna = lift(pa, ll, 'L e. Word 2o'), lift(pa, nn, 'N e. NN0'), lift(pa, vv, 'V e. TMSt'), lift(pa, ln, '%s e. NN0' % LN)
    ca = Closure(w, pa, {'N': ('NN0', nna), LN: ('NN0', lna)})
    le = w.s([ca.mem('N', 'RR'), ca.mem(LN, 'RR'), lt], 'ltled', '( %s -> N <_ %s )' % (pa, LN))
    inR = w.s([w.s([nna, lna, le], '3jca', '( %s -> ( N e. NN0 /\\ %s e. NN0 /\\ N <_ %s ) )' % (pa, LN, LN)),
               w.s([], 'elfz2nn0', '( N e. %s <-> ( N e. NN0 /\\ %s e. NN0 /\\ N <_ %s ) )' % (R, LN, LN))], 'sylibr', '( %s -> N e. %s )' % (pa, R))
    Z = '<. 1 , ( L ` N ) >.'
    uz = uvalue(pa, nna, lla, Z, True, lt)
    ez = w.s([ca.mem('N', 'ZZ'), closed(w, pa, '0z', '0 e. ZZ'), ca.mem(LN, 'ZZ'), w.inst('elfzo')], 'syl3anc',
             '( %s -> ( N e. ( 0 ..^ %s ) <-> ( 0 <_ N /\\ N < %s ) ) )' % (pa, LN, LN))
    nfo = w.s([ez, w.s([ca.ge0('N'), lt], 'jca', '( %s -> ( 0 <_ N /\\ N < %s ) )' % (pa, LN))], 'mpbird', '( %s -> N e. ( 0 ..^ %s ) )' % (pa, LN))
    lnb = w.s([lla, nfo, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> ( L ` N ) e. 2o )' % pa)
    fi = w.s([closed(w, pa, 'tmcinclf', 'inclBool : 2o --> %s' % BITS), lnb], 'ffvelcdmd', '( %s -> ( inclBool ` ( L ` N ) ) e. %s )' % (pa, BITS))
    zz = w.s([w.s([lnb, w.inst('inclboolfv')], 'syl', '( %s -> ( inclBool ` ( L ` N ) ) = %s )' % (pa, Z)), fi], 'eqeltrrd', '( %s -> %s e. %s )' % (pa, Z, BITS))
    nv = rd_bit(w, pa, h, 'V', Z, vva, zz)
    mem, flds = readcase(pa, Z, uz, nv, inR)
    # the register: ( inl ` ( 2nd ` Z ) ) = ( inl ` ( L ` N ) ) = RGV
    s2 = w.s([closed(w, pa, '1ex', '1 e. _V'), w.s([lnb], 'elexd', '( %s -> ( L ` N ) e. _V )' % pa), w.inst('op2ndg')], 'syl2anc',
             '( %s -> ( 2nd ` %s ) = ( L ` N ) )' % (pa, Z))
    rg1 = w.s([flds[sd['reg']], w.s([s2], 'fveq2d', '( %s -> ( inl ` ( 2nd ` %s ) ) = ( inl ` ( L ` N ) ) )' % (pa, Z))], 'eqtrd',
              '( %s -> ( %s ` %s ) = ( inl ` ( L ` N ) ) )' % (pa, REG, n1))
    rgt = w.s([lt], 'iftrued', '( %s -> %s = ( inl ` ( L ` N ) ) )' % (pa, RGV('L', 'N')))
    rg = w.s([rg1, rgt], 'eqtr4d', '( %s -> ( %s ` %s ) = %s )' % (pa, REG, n1, RGV('L', 'N')))
    # the flag: stays [ |L| < N ] = (/) = [ |L| <_ N ]
    nlt = w.s([le, w.s([ca.mem('N', 'RR'), ca.mem(LN, 'RR')], 'lenltd' if False else 'lenltd', '( %s -> ( N <_ %s <-> -. %s < N ) )' % (pa, LN, LN))], 'mpbid',
              '( %s -> -. %s < N )' % (pa, LN))
    nle = w.s([lt, w.s([ca.mem('N', 'RR'), ca.mem(LN, 'RR')], 'ltnled', '( %s -> ( N < %s <-> -. %s <_ N ) )' % (pa, LN, LN))], 'mpbid',
              '( %s -> -. %s <_ N )' % (pa, LN))
    fv0 = w.s([lift(pa, vfl, '( %s ` V ) = %s' % (FLAG, FLG('L', '<', 'N'))), w.s([nlt], 'iffalsed', '( %s -> %s = (/) )' % (pa, FLG('L', '<', 'N')))],
              'eqtrd', '( %s -> ( %s ` V ) = (/) )' % (pa, FLAG))
    fl1 = w.s([flds[sd['flag']], fv0], 'eqtrd', '( %s -> ( %s ` %s ) = (/) )' % (pa, FLAG, n1))
    fl = w.s([fl1, w.s([nle], 'iffalsed', '( %s -> %s = (/) )' % (pa, FLG('L', '<_', 'N')))], 'eqtr4d',
             '( %s -> ( %s ` %s ) = %s )' % (pa, FLAG, n1, FLG('L', '<_', 'N')))
    caseA = finish(pa, mem, fl, rg, flds)
    # ---------------- case N = |L|
    pb = '( %s /\\ N = %s )' % (ph, LN)
    eqb = w.s([], 'simpr', '( %s -> N = %s )' % (pb, LN))
    llb, nnb, vvb, lnb_ = lift(pb, ll, 'L e. Word 2o'), lift(pb, nn, 'N e. NN0'), lift(pb, vv, 'V e. TMSt'), lift(pb, ln, '%s e. NN0' % LN)
    cb = Closure(w, pb, {'N': ('NN0', nnb), LN: ('NN0', lnb_)})
    leb = w.s([cb.mem('N', 'RR'), eqb], 'eqled', '( %s -> N <_ %s )' % (pb, LN))
    inRb = w.s([w.s([nnb, lnb_, leb], '3jca', '( %s -> ( N e. NN0 /\\ %s e. NN0 /\\ N <_ %s ) )' % (pb, LN, LN)),
                w.s([], 'elfz2nn0', '( N e. %s <-> ( N e. NN0 /\\ %s e. NN0 /\\ N <_ %s ) )' % (R, LN, LN))], 'sylibr', '( %s -> N e. %s )' % (pb, R))
    nltb = w.s([w.s([eqb], 'breq1d', '( %s -> ( N < %s <-> %s < %s ) )' % (pb, LN, LN, LN)), w.s([cb.mem(LN, 'RR')], 'ltnrd', '( %s -> -. %s < %s )' % (pb, LN, LN))],
               'mtbird', '( %s -> -. N < %s )' % (pb, LN))
    uzb = uvalue(pb, nnb, llb, '4', False, nltb)
    nvb = rd_comma(w, pb, h, 'V', vvb)
    memb, fldb = readcase(pb, '4', uzb, nvb, inRb)
    rgb = w.s([fldb[sd['reg']], w.s([nltb], 'iffalsed', '( %s -> %s = ( inr ` (/) ) )' % (pb, RGV('L', 'N')))], 'eqtr4d',
              '( %s -> ( %s ` %s ) = %s )' % (pb, REG, n1, RGV('L', 'N')))
    leb2 = w.s([cb.mem(LN, 'RR'), w.s([eqb], 'eqcomd', '( %s -> %s = N )' % (pb, LN))], 'eqled', '( %s -> %s <_ N )' % (pb, LN))
    flb = w.s([fldb[sd['flag']], w.s([leb2], 'iftrued', '( %s -> %s = 1o )' % (pb, FLG('L', '<_', 'N')))], 'eqtr4d',
              '( %s -> ( %s ` %s ) = %s )' % (pb, FLAG, n1, FLG('L', '<_', 'N')))
    caseB = finish(pb, memb, flb, rgb, fldb)
    # ---------------- case |L| < N
    pc = '( %s /\\ %s < N )' % (ph, LN)
    ltc = w.s([], 'simpr', '( %s -> %s < N )' % (pc, LN))
    nnc, vvc, lnc = lift(pc, nn, 'N e. NN0'), lift(pc, vv, 'V e. TMSt'), lift(pc, ln, '%s e. NN0' % LN)
    cc = Closure(w, pc, {'N': ('NN0', nnc), LN: ('NN0', lnc)})
    nlec = w.s([ltc, w.s([cc.mem(LN, 'RR'), cc.mem('N', 'RR')], 'ltnled', '( %s -> ( %s < N <-> -. N <_ %s ) )' % (pc, LN, LN))], 'mpbid',
               '( %s -> -. N <_ %s )' % (pc, LN))
    fzle = w.s([w.s([], 'elfzle2', '( N e. %s -> N <_ %s )' % (R, LN))], 'a1i', '( %s -> ( N e. %s -> N <_ %s ) )' % (pc, R, LN))
    ninR = w.s([nlec, fzle], 'mtod', '( %s -> -. N e. %s )' % (pc, R))
    itc = w.s([ninR], 'iffalsed', '( %s -> %s = V )' % (pc, n1))
    memc = w.s([itc, vvc], 'eqeltrd', '( %s -> %s e. TMSt )' % (pc, n1))
    fldc = {f: w.s([itc], 'fveq2d', '( %s -> ( %s ` %s ) = ( %s ` V ) )' % (pc, ACC[f], n1, ACC[f])) for f in ORDER}
    lec = w.s([cc.mem(LN, 'RR'), cc.mem('N', 'RR'), ltc], 'ltled', '( %s -> %s <_ N )' % (pc, LN))
    nltc = w.s([lec, w.s([cc.mem(LN, 'RR'), cc.mem('N', 'RR')], 'lenltd', '( %s -> ( %s <_ N <-> -. N < %s ) )' % (pc, LN, LN))], 'mpbid',
               '( %s -> -. N < %s )' % (pc, LN))
    vrgc = w.s([ltc, lift(pc, vrg, '( %s < N -> ( %s ` V ) = ( inr ` (/) ) )' % (LN, REG))], 'mpd', '( %s -> ( %s ` V ) = ( inr ` (/) ) )' % (pc, REG))
    rgc = w.s([w.s([fldc[sd['reg']], vrgc], 'eqtrd', '( %s -> ( %s ` %s ) = ( inr ` (/) ) )' % (pc, REG, n1)),
               w.s([nltc], 'iffalsed', '( %s -> %s = ( inr ` (/) ) )' % (pc, RGV('L', 'N')))], 'eqtr4d',
              '( %s -> ( %s ` %s ) = %s )' % (pc, REG, n1, RGV('L', 'N')))
    fv1 = w.s([lift(pc, vfl, '( %s ` V ) = %s' % (FLAG, FLG('L', '<', 'N'))), w.s([ltc], 'iftrued', '( %s -> %s = 1o )' % (pc, FLG('L', '<', 'N')))],
              'eqtrd', '( %s -> ( %s ` V ) = 1o )' % (pc, FLAG))
    flc = w.s([w.s([fldc[sd['flag']], fv1], 'eqtrd', '( %s -> ( %s ` %s ) = 1o )' % (pc, FLAG, n1)),
               w.s([lec], 'iftrued', '( %s -> %s = 1o )' % (pc, FLG('L', '<_', 'N')))], 'eqtr4d',
              '( %s -> ( %s ` %s ) = %s )' % (pc, FLAG, n1, FLG('L', '<_', 'N')))
    caseC = finish(pc, memc, flc, rgc, fldc)
    # ---------------- the three cases
    c0 = Closure(w, ph, {'N': ('NN0', nn), LN: ('NN0', ln)})
    ab = w.s([caseA, caseB], 'jaodan', '( ( %s /\\ ( N < %s \\/ N = %s ) ) -> %s )' % (ph, LN, LN, G))
    lo = w.s([c0.mem('N', 'RR'), c0.mem(LN, 'RR'), w.inst('leloe')], 'syl2anc', '( %s -> ( N <_ %s <-> ( N < %s \\/ N = %s ) ) )' % (ph, LN, LN, LN))
    loa = w.s([lo], 'biimpa', '( ( %s /\\ N <_ %s ) -> ( N < %s \\/ N = %s ) )' % (ph, LN, LN, LN))
    le_ = w.s([loa, ab], 'syldan', '( ( %s /\\ N <_ %s ) -> %s )' % (ph, LN, G))
    abc = w.s([le_, caseC], 'jaodan', '( ( %s /\\ ( N <_ %s \\/ %s < N ) ) -> %s )' % (ph, LN, LN, G))
    tri = w.s([c0.mem('N', 'RR'), c0.mem(LN, 'RR'), w.inst('lelttric')], 'syl2anc', '( %s -> ( N <_ %s \\/ %s < N ) )' % (ph, LN, LN))
    w.qed([tri, abc], 'mpdan', '( %s -> %s )' % (ph, G))
    return w.run()


if __name__ == '__main__':
    if want('tmcrda'): tmcrd('A')
    if want('tmcrdb'): tmcrd('B')
