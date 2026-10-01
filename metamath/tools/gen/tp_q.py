"""Sortie TP: the core for any finite index set (tpmaxn: enumerate I, pad with zeros to length N, apply ~ tpcore)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
import tplib
from tplib import S, W, Closure, ap, apc, lin, lift, WIN, CN
import cl as _cl
import ef2lib as E
import mvlib
from z4blib import fvmd

only = sys.argv[1:]
conj, up, body_of, top_and, ante_of, tsub = E.conj, E.up, E.body_of, E.top_and, E.ante_of, E.tsub
stmt = tplib.stmt


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


X0 = '( 0 ..^ N )'
A_ = '( # ` I )'
XA = '( 0 ..^ %s )' % A_
PSI = lambda k: 'sum_ j e. I ( ( W ` j ) ^ %s )' % k
NA = ('( ( N e. NN /\\ 2 <_ N /\\ M e. NN0 ) /\\ ( I e. Fin /\\ %s <_ N /\\ W : I --> CC ) /\\ '
      '( X e. I /\\ A. y e. I ( abs ` ( W ` y ) ) <_ 1 /\\ ( W ` X ) = 1 ) )' % A_)
S['tpmaxn'] = '( %s -> E. k e. %s %s <_ ( abs ` %s ) )' % (NA, WIN(), CN(), PSI('k'))


def gen_maxn():
    w = W('tpmaxn', 'Lean ` core_norm_bound ` for any finite index set of at most N entries (enumerate, pad with zeros, ~ tpcore ).')
    A0 = NA
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    t1 = s([], 'simp1', '( N e. NN /\\ 2 <_ N /\\ M e. NN0 )'); t2 = s([], 'simp2', '( I e. Fin /\\ %s <_ N /\\ W : I --> CC )' % A_)
    t3 = s([], 'simp3', '( X e. I /\\ A. y e. I ( abs ` ( W ` y ) ) <_ 1 /\\ ( W ` X ) = 1 )')
    nn = s([t1], 'simp1d', 'N e. NN'); mm = s([t1], 'simp3d', 'M e. NN0')
    ifin = s([t2], 'simp1d', 'I e. Fin'); ale = s([t2], 'simp2d', '%s <_ N' % A_); wf = s([t2], 'simp3d', 'W : I --> CC')
    xi = s([t3], 'simp1d', 'X e. I'); wb = s([t3], 'simp2d', 'A. y e. I ( abs ` ( W ` y ) ) <_ 1'); wx1 = s([t3], 'simp3d', '( W ` X ) = 1')
    an0 = s([ifin, w.inst('hashcl')], 'syl', '%s e. NN0' % A_)
    c = Closure(w, A0, {'N': ('NN', nn), 'M': ('NN0', mm), A_: ('NN0', an0)})
    afz = ap(w, A0, 'elfzd', '%s e. ( 0 ... N )' % A_, c, facts=[s([w.s([], '0z', '0 e. ZZ')], 'a1i', '0 e. ZZ'), c.mem('N', 'ZZ'), c.mem(A_, 'ZZ'), c.ge0(A_), ale])
    ass = s([s([afz, w.inst('elfzuz3')], 'syl', 'N e. ( ZZ>= ` %s )' % A_), w.inst('fzoss2')], 'syl', '%s C_ %s' % (XA, X0))
    fza = s([w.s([], 'fzofi', '%s e. Fin' % XA)], 'a1i', '%s e. Fin' % XA)
    ex = s([s([an0, w.inst('hashfzo0')], 'syl', '( # ` %s ) = %s' % (XA, A_)), s([fza, ifin, w.inst('hasheqf1o')], 'syl2anc',
                                                                                       '( ( # ` %s ) = %s <-> E. e e : %s -1-1-onto-> I )' % (XA, A_, XA))], 'mpbid',
            'E. e e : %s -1-1-onto-> I' % XA)
    EF = 'e : %s -1-1-onto-> I' % XA
    E1 = '( %s /\\ %s )' % (A0, EF)
    se = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (E1, f))
    LE = lambda st: _cl.lift(w, st, E1)
    ef = w.s([], 'simpr', '( %s -> %s )' % (E1, EF))
    eff = se([ef, w.inst('f1of')], 'syl', 'e : %s --> I' % XA)
    VB = 'if ( h e. %s , ( W ` ( e ` h ) ) , 0 )' % XA
    VV = '( h e. %s |-> %s )' % (X0, VB)

    def val(K, a, ain):
        idh = w.s([], 'id', '( h = %s -> h = %s )' % (a, a))
        cg, v = w.congr(VB, {'h': a}, 'h = %s' % a, {'h': idh})
        ex_ = w.s([w.s([], 'fvex', '( W ` ( e ` %s ) ) e. _V' % a), w.s([], 'c0ex', '0 e. _V')], 'ifex', '%s e. _V' % v)
        st = w.s([cg, w.s([], 'eqid', '%s = %s' % (VV, VV)), ex_], 'fvmpt', '( %s e. %s -> ( %s ` %s ) = %s )' % (a, X0, VV, a, v))
        return w.s([ain, st], 'syl', '( %s -> ( %s ` %s ) = %s )' % (K, VV, a, v)), v
    Kh = '( %s /\\ h e. %s )' % (E1, X0)
    Kin = '( %s /\\ h e. %s )' % (Kh, XA)
    Kout = '( %s /\\ -. h e. %s )' % (Kh, XA)
    weh = w.s([_cl.lift(w, LE(wf), Kin), w.s([_cl.lift(w, eff, Kin), w.s([], 'simpr', '( %s -> h e. %s )' % (Kin, XA))], 'ffvelcdmd', '( %s -> ( e ` h ) e. I )' % Kin)],
              'ffvelcdmd', '( %s -> ( W ` ( e ` h ) ) e. CC )' % Kin)
    vcc = w.s([weh, w.s([], '0cnd', '( %s -> 0 e. CC )' % Kout)], 'ifclda', '( %s -> %s e. CC )' % (Kh, VB))
    vvf = se([vcc, w.s([], 'eqid', '%s = %s' % (VV, VV))], 'fmptd', '%s : %s --> CC' % (VV, X0))
    Kr = '( %s /\\ r e. %s )' % (E1, X0)
    vr, vrt = val(Kr, 'r', w.s([], 'simpr', '( %s -> r e. %s )' % (Kr, X0)))
    Krin = '( %s /\\ r e. %s )' % (Kr, XA)
    Krout = '( %s /\\ -. r e. %s )' % (Kr, XA)
    erI = w.s([_cl.lift(w, eff, Krin), w.s([], 'simpr', '( %s -> r e. %s )' % (Krin, XA))], 'ffvelcdmd', '( %s -> ( e ` r ) e. I )' % Krin)
    idy = w.s([], 'id', '( y = ( e ` r ) -> y = ( e ` r ) )')
    cgy, ny = w.wcongr('( abs ` ( W ` y ) ) <_ 1', {'y': '( e ` r )'}, 'y = ( e ` r )', {'y': idy})
    b1 = w.s([erI, _cl.lift(w, LE(wb), Krin), w.s([cgy], 'rspcv', '( ( e ` r ) e. I -> ( A. y e. I ( abs ` ( W ` y ) ) <_ 1 -> %s ) )' % ny)], 'sylc', '( %s -> %s )' % (Krin, ny))
    i1 = w.s([w.s([w.s([], 'simpr', '( %s -> r e. %s )' % (Krin, XA))], 'iftrued', '( %s -> %s = ( W ` ( e ` r ) ) )' % (Krin, vrt))], 'fveq2d',
             '( %s -> ( abs ` %s ) = ( abs ` ( W ` ( e ` r ) ) ) )' % (Krin, vrt))
    case1 = w.s([i1, b1], 'eqbrtrd', '( %s -> ( abs ` %s ) <_ 1 )' % (Krin, vrt))
    i2 = w.s([w.s([w.s([], 'simpr', '( %s -> -. r e. %s )' % (Krout, XA))], 'iffalsed', '( %s -> %s = 0 )' % (Krout, vrt))], 'fveq2d',
             '( %s -> ( abs ` %s ) = ( abs ` 0 ) )' % (Krout, vrt))
    i3 = w.s([i2, w.s([w.s([], 'abs0', '( abs ` 0 ) = 0')], 'a1i', '( %s -> ( abs ` 0 ) = 0 )' % Krout)], 'eqtrd', '( %s -> ( abs ` %s ) = 0 )' % (Krout, vrt))
    case2 = w.s([i3, w.s([w.s([], '0le1', '0 <_ 1')], 'a1i', '( %s -> 0 <_ 1 )' % Krout)], 'eqbrtrd', '( %s -> ( abs ` %s ) <_ 1 )' % (Krout, vrt))
    br = w.s([case1, case2], 'pm2.61dan', '( %s -> ( abs ` %s ) <_ 1 )' % (Kr, vrt))
    br2 = w.s([w.s([vr], 'fveq2d', '( %s -> ( abs ` ( %s ` r ) ) = ( abs ` %s ) )' % (Kr, VV, vrt)), br], 'eqbrtrd', '( %s -> ( abs ` ( %s ` r ) ) <_ 1 )' % (Kr, VV))
    vb = w.s([br2], 'ralrimiva', '( %s -> A. r e. %s ( abs ` ( %s ` r ) ) <_ 1 )' % (E1, X0, VV))
    JJ = "( `' e ` X )"
    jA = se([ef, LE(xi), w.inst('f1ocnvdm')], 'syl2anc', '%s e. %s' % (JJ, XA))
    jN = se([LE(ass), jA], 'sseldd', '%s e. %s' % (JJ, X0))
    vj, vjt = val(E1, JJ, jN)
    v1 = se([vj, se([jA], 'iftrued', '%s = ( W ` ( e ` %s ) )' % (vjt, JJ))], 'eqtrd', '( %s ` %s ) = ( W ` ( e ` %s ) )' % (VV, JJ, JJ))
    v2 = se([se([ef, LE(xi), w.inst('f1ocnvfv2')], 'syl2anc', '( e ` %s ) = X' % JJ)], 'fveq2d', '( W ` ( e ` %s ) ) = ( W ` X )' % JJ)
    vj1 = se([v1, v2, LE(wx1)], '3eqtrd', '( %s ` %s ) = 1' % (VV, JJ))
    CO = tsub(stmt('tpcore'), {'V': VV, 'J': JJ})
    ca, cc = ante_of(CO)
    have = {'( N e. NN /\\ 2 <_ N /\\ M e. NN0 )': LE(t1), '%s : %s --> CC' % (VV, X0): vvf, body_of(w, vb): vb, '%s e. %s' % (JJ, X0): jN, '( %s ` %s ) = 1' % (VV, JJ): vj1}
    core = se([conj(w, E1, ca, have), w.inst('tpcore')], 'syl', cc)
    PSV = cc.split('( abs ` ', 1)[1][:-2]
    Ek = '( %s /\\ k e. %s )' % (E1, WIN())
    sk = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Ek, f))
    kin = w.s([], 'simpr', '( %s -> k e. %s )' % (Ek, WIN()))
    ck = Closure(w, Ek, {'M': ('NN0', _cl.lift(w, LE(mm), Ek)), 'k': ('ZZ', w.s([kin, w.inst('elfzelz')], 'syl', '( %s -> k e. ZZ )' % Ek))})
    kle = w.s([kin, w.inst('elfzle1')], 'syl', '( %s -> ( M + 1 ) <_ k )' % Ek)
    kpos = lin.linarith(w, Ek, [kle, ck.ge0('M')], '0 < k', closure=ck)
    knn = w.s([w.s([ck.mem('k', 'ZZ'), kpos], 'jca', '( %s -> ( k e. ZZ /\\ 0 < k ) )' % Ek), w.inst('elnnz')], 'sylibr', '( %s -> k e. NN )' % Ek)
    kn0 = w.s([knn], 'nnnn0d', '( %s -> k e. NN0 )' % Ek)
    spl = sk([_cl.lift(w, afz, Ek), w.inst('fzosplit')], 'syl', '%s = ( %s u. ( %s ..^ N ) )' % (X0, XA, A_))
    Ekj = '( %s /\\ j e. %s )' % (Ek, X0)
    vjc = w.s([_cl.lift(w, vvf, Ekj), w.s([], 'simpr', '( %s -> j e. %s )' % (Ekj, X0))], 'ffvelcdmd', '( %s -> ( %s ` j ) e. CC )' % (Ekj, VV))
    body = w.s([vjc, _cl.lift(w, kn0, Ekj)], 'expcld', '( %s -> ( ( %s ` j ) ^ k ) e. CC )' % (Ekj, VV))
    fs = sk([sk([w.s([], 'fzodisj', '( %s i^i ( %s ..^ N ) ) = (/)' % (XA, A_))], 'a1i', '( %s i^i ( %s ..^ N ) ) = (/)' % (XA, A_)), spl,
             sk([w.s([], 'fzofi', '%s e. Fin' % X0)], 'a1i', '%s e. Fin' % X0), body], 'fsumsplit',
            '%s = ( sum_ j e. %s ( ( %s ` j ) ^ k ) + sum_ j e. ( %s ..^ N ) ( ( %s ` j ) ^ k ) )' % (PSV, XA, VV, A_, VV))
    Eka = '( %s /\\ j e. %s )' % (Ek, XA)
    ja = w.s([], 'simpr', '( %s -> j e. %s )' % (Eka, XA))
    jn_ = w.s([_cl.lift(w, LE(ass), Eka), ja], 'sseldd', '( %s -> j e. %s )' % (Eka, X0))
    va, vat = val(Eka, 'j', jn_)
    va2 = w.s([va, w.s([ja], 'iftrued', '( %s -> %s = ( W ` ( e ` j ) ) )' % (Eka, vat))], 'eqtrd', '( %s -> ( %s ` j ) = ( W ` ( e ` j ) ) )' % (Eka, VV))
    p1 = sk([w.s([va2], 'oveq1d', '( %s -> ( ( %s ` j ) ^ k ) = ( ( W ` ( e ` j ) ) ^ k ) )' % (Eka, VV))], 'sumeq2dv',
            'sum_ j e. %s ( ( %s ` j ) ^ k ) = sum_ j e. %s ( ( W ` ( e ` j ) ) ^ k )' % (XA, VV, XA))
    Ekb = '( %s /\\ j e. ( %s ..^ N ) )' % (Ek, A_)
    jb = w.s([], 'simpr', '( %s -> j e. ( %s ..^ N ) )' % (Ekb, A_))
    dj2 = w.s([w.s([w.s([], 'incom', '( ( %s ..^ N ) i^i %s ) = ( %s i^i ( %s ..^ N ) )' % (A_, XA, XA, A_)), w.s([], 'fzodisj', '( %s i^i ( %s ..^ N ) ) = (/)' % (XA, A_))],
                   'eqtri', '( ( %s ..^ N ) i^i %s ) = (/)' % (A_, XA))], 'a1i', '( %s -> ( ( %s ..^ N ) i^i %s ) = (/) )' % (Ekb, A_, XA))
    jn2 = w.s([w.s([dj2, jb], 'jca', '( %s -> ( ( ( %s ..^ N ) i^i %s ) = (/) /\\ j e. ( %s ..^ N ) ) )' % (Ekb, A_, XA, A_)), w.inst('disjel')], 'syl', '( %s -> -. j e. %s )' % (Ekb, XA))
    jNb = w.s([w.s([w.s([w.s([], 'ssun2', '( %s ..^ N ) C_ ( %s u. ( %s ..^ N ) )' % (A_, XA, A_))], 'a1i', '( %s -> ( %s ..^ N ) C_ ( %s u. ( %s ..^ N ) ) )' % (Ekb, A_, XA, A_)),
                    w.s([_cl.lift(w, spl, Ekb)], 'eqcomd', '( %s -> ( %s u. ( %s ..^ N ) ) = %s )' % (Ekb, XA, A_, X0))], 'sseqtrd', '( %s -> ( %s ..^ N ) C_ %s )' % (Ekb, A_, X0)), jb],
               'sseldd', '( %s -> j e. %s )' % (Ekb, X0))
    vb_, vbt = val(Ekb, 'j', jNb)
    vb2 = w.s([vb_, w.s([jn2], 'iffalsed', '( %s -> %s = 0 )' % (Ekb, vbt))], 'eqtrd', '( %s -> ( %s ` j ) = 0 )' % (Ekb, VV))
    z1 = w.s([w.s([vb2], 'oveq1d', '( %s -> ( ( %s ` j ) ^ k ) = ( 0 ^ k ) )' % (Ekb, VV)), w.s([_cl.lift(w, knn, Ekb)], '0expd', '( %s -> ( 0 ^ k ) = 0 )' % Ekb)], 'eqtrd',
             '( %s -> ( ( %s ` j ) ^ k ) = 0 )' % (Ekb, VV))
    p2 = sk([z1], 'sumeq2dv', 'sum_ j e. ( %s ..^ N ) ( ( %s ` j ) ^ k ) = sum_ j e. ( %s ..^ N ) 0' % (A_, VV, A_))
    p3 = sk([sk([sk([w.s([], 'fzofi', '( %s ..^ N ) e. Fin' % A_)], 'a1i', '( %s ..^ N ) e. Fin' % A_)], 'olcd', '( ( %s ..^ N ) C_ ( ZZ>= ` 0 ) \\/ ( %s ..^ N ) e. Fin )' % (A_, A_)),
             w.inst('sumz')], 'syl', 'sum_ j e. ( %s ..^ N ) 0 = 0' % A_)
    idjq = w.s([], 'id', '( j = ( e ` q ) -> j = ( e ` q ) )')
    cjq, _ = w.congr('( ( W ` j ) ^ k )', {'j': '( e ` q )'}, 'j = ( e ` q )', {'j': idjq})
    EkI = '( %s /\\ j e. I )' % Ek
    wjc = w.s([w.s([_cl.lift(w, LE(wf), EkI), w.s([], 'simpr', '( %s -> j e. I )' % EkI)], 'ffvelcdmd', '( %s -> ( W ` j ) e. CC )' % EkI), _cl.lift(w, kn0, EkI)],
              'expcld', '( %s -> ( ( W ` j ) ^ k ) e. CC )' % EkI)
    Ekq = '( %s /\\ q e. %s )' % (Ek, XA)
    fo = sk([cjq, sk([w.s([], 'fzofi', '%s e. Fin' % XA)], 'a1i', '%s e. Fin' % XA), _cl.lift(w, ef, Ek), w.s([], 'eqidd', '( %s -> ( e ` q ) = ( e ` q ) )' % Ekq), wjc],
            'fsumf1o', '%s = sum_ q e. %s ( ( W ` ( e ` q ) ) ^ k )' % (PSI('k'), XA))
    idjq2 = w.s([], 'id', '( j = q -> j = q )')
    cjq2, _ = w.congr('( ( W ` ( e ` j ) ) ^ k )', {'j': 'q'}, 'j = q', {'j': idjq2})
    cbs = w.s([cjq2], 'cbvsumv', 'sum_ j e. %s ( ( W ` ( e ` j ) ) ^ k ) = sum_ q e. %s ( ( W ` ( e ` q ) ) ^ k )' % (XA, XA))
    fo2 = sk([fo, sk([cbs], 'a1i', tplib.formula_of_step(w, cbs))], 'eqtr4d', '%s = sum_ j e. %s ( ( W ` ( e ` j ) ) ^ k )' % (PSI('k'), XA))
    tot = sk([fs, sk([p1, sk([p2, p3], 'eqtrd', 'sum_ j e. ( %s ..^ N ) ( ( %s ` j ) ^ k ) = 0' % (A_, VV))], 'oveq12d',
                     '( sum_ j e. %s ( ( %s ` j ) ^ k ) + sum_ j e. ( %s ..^ N ) ( ( %s ` j ) ^ k ) ) = ( sum_ j e. %s ( ( W ` ( e ` j ) ) ^ k ) + 0 )' % (XA, VV, A_, VV, XA))], 'eqtrd',
             '%s = ( sum_ j e. %s ( ( W ` ( e ` j ) ) ^ k ) + 0 )' % (PSV, XA))
    psic = sk([_cl.lift(w, LE(ifin), Ek), wjc], 'fsumcl', '%s e. CC' % PSI('k'))
    tot2 = sk([tot, sk([sk([fo2], 'eqcomd', 'sum_ j e. %s ( ( W ` ( e ` j ) ) ^ k ) = %s' % (XA, PSI('k')))], 'oveq1d',
                       '( sum_ j e. %s ( ( W ` ( e ` j ) ) ^ k ) + 0 ) = ( %s + 0 )' % (XA, PSI('k'))), sk([psic], 'addridd', '( %s + 0 ) = %s' % (PSI('k'), PSI('k')))],
              '3eqtrd', '%s = %s' % (PSV, PSI('k')))
    imp = sk([sk([tot2], 'fveq2d', '( abs ` %s ) = ( abs ` %s )' % (PSV, PSI('k')))], 'breq2d', '( %s <_ ( abs ` %s ) <-> %s <_ ( abs ` %s ) )' % (CN(), PSV, CN(), PSI('k')))
    imp = sk([imp], 'biimpd', '( %s <_ ( abs ` %s ) -> %s <_ ( abs ` %s ) )' % (CN(), PSV, CN(), PSI('k')))
    rx = se([imp], 'reximdva', '( E. k e. %s %s <_ ( abs ` %s ) -> E. k e. %s %s <_ ( abs ` %s ) )' % (WIN(), CN(), PSV, WIN(), CN(), PSI('k')))
    GOAL = 'E. k e. %s %s <_ ( abs ` %s )' % (WIN(), CN(), PSI('k'))
    fin = se([core, rx], 'mpd', GOAL)
    f2 = w.s([fin], 'ex', '( %s -> ( %s -> %s ) )' % (A0, EF, GOAL))
    f3 = w.s([f2], 'exlimdv', '( %s -> ( E. e %s -> %s ) )' % (A0, EF, GOAL))
    w.qed([ex, f3], 'mpd', S['tpmaxn'])
    return run(w)


if __name__ == '__main__':
    gen_maxn()
