"""Sortie C2 section 3.1b: derived holomorphic functions (power, product, quotient)."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c2_lib import *

DVF = '( CC _D F )'
DVG = '( CC _D G )'
FZ = '( F ` z )'; GZ = '( G ` z )'
DFZ = '( %s ` z )' % DVF; DGZ = '( %s ` z )' % DVG


def holctx(w, A0, hl, Fn='F'):
    """from a step hl: ( A0 -> HOL(Fn) ) return (fcn, dd, dcc, ff, fmpt, dvmpt)"""
    dv = '( CC _D %s )' % Fn
    fcn = w.s([hl, w.inst('simpl')], 'syl', '( %s -> %s e. ( D -cn-> CC ) )' % (A0, Fn))
    dd = w.s([hl, w.inst('simpr')], 'syl', '( %s -> D C_ dom %s )' % (A0, dv))
    dcc = w.s([fcn, w.inst('cncfrss')], 'syl', '( %s -> D C_ CC )' % A0)
    ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> %s : D --> CC )' % (A0, Fn))
    fmpt = w.s([ff], 'feqmptd', '( %s -> %s = %s )' % (A0, Fn, MP('z', 'D', '( %s ` z )' % Fn)))
    dvm = w.s([hl, w.inst('holdv')], 'syl', '( %s -> ( CC _D %s ) = %s )' % (
        A0, MP('z', 'D', '( %s ` z )' % Fn), MP('z', 'D', '( %s ` z )' % dv)))
    dvf = w.s([hl, w.inst('holf')], 'syl', '( %s -> %s : D --> CC )' % (A0, dv))
    return fcn, dd, dcc, ff, fmpt, dvm, dvf


def cnel(w, A0):
    return w.s([w.s([], 'cnelprrecn', 'CC e. { RR , CC }')], 'a1i', '( %s -> CC e. { RR , CC } )' % A0)


# ---- holexp ----------------------------------------------------------------
w = W('holexp', 'A positive integer power of a function holomorphic on its whole domain is holomorphic on that domain.')
A0 = '( %s /\\ N e. NN )' % HOL
A1 = '( %s /\\ z e. D )' % A0
A2 = '( %s /\\ y e. CC )' % A0
MPN = MP('z', 'D', '( %s ^ N )' % FZ)
hl = w.s([], 'simpl', '( %s -> %s )' % (A0, HOL))
nn = w.s([], 'simpr', '( %s -> N e. NN )' % A0)
nn0 = w.s([nn, w.inst('nnnn0')], 'syl', '( %s -> N e. NN0 )' % A0)
fcn, dd, dcc, ff, fmpt, dvm, dvf = holctx(w, A0, hl)
# continuity
fmp = w.s([fmpt, fcn], 'eqeltrrd', '( %s -> %s e. ( D -cn-> CC ) )' % (A0, MP('z', 'D', FZ)))
cnc = w.s([fmp, nn0, w.inst('cncfexpb')], 'syl2anc', '( %s -> %s e. ( D -cn-> CC ) )' % (A0, MPN))
# derivative by dvmptco with dvexp
ce1 = cnel(w, A0); ce2 = cnel(w, A0)
zD = w.s([], 'simpr', '( %s -> z e. D )' % A1)
fzc = w.s([w.s([ff], 'adantr', '( %s -> F : D --> CC )' % A1), zD], 'ffvelcdmd', '( %s -> %s e. CC )' % (A1, FZ))
dfzc = w.s([w.s([dvf], 'adantr', '( %s -> %s : D --> CC )' % (A1, DVF)), zD], 'ffvelcdmd', '( %s -> %s e. CC )' % (A1, DFZ))
yc = w.s([], 'simpr', '( %s -> y e. CC )' % A2)
n0a = w.s([nn0], 'adantr', '( %s -> N e. NN0 )' % A2)
ync = w.s([yc, n0a], 'expcld', '( %s -> ( y ^ N ) e. CC )' % A2)
nca = w.s([w.s([nn], 'adantr', '( %s -> N e. NN )' % A2), w.inst('nncnd')], 'syl', '( %s -> N e. CC )' % A2) if False else w.s([w.s([nn], 'adantr', '( %s -> N e. NN )' % A2)], 'nncnd', '( %s -> N e. CC )' % A2)
nm1 = w.s([w.s([nn], 'adantr', '( %s -> N e. NN )' % A2), w.inst('nnm1nn0')], 'syl', '( %s -> ( N - 1 ) e. NN0 )' % A2)
ynm = w.s([nca, w.s([yc, nm1], 'expcld', '( %s -> ( y ^ ( N - 1 ) ) e. CC )' % A2)], 'mulcld', '( %s -> ( N x. ( y ^ ( N - 1 ) ) ) e. CC )' % A2)
dex = w.s([nn, w.inst('dvexp')], 'syl', '( %s -> ( CC _D %s ) = %s )' % (A0, MP('y', 'CC', '( y ^ N )'), MP('y', 'CC', '( N x. ( y ^ ( N - 1 ) ) )')))
se = w.s([], 'oveq1', '( y = %s -> ( y ^ N ) = ( %s ^ N ) )' % (FZ, FZ))
sf = w.s([w.s([], 'oveq1', '( y = %s -> ( y ^ ( N - 1 ) ) = ( %s ^ ( N - 1 ) ) )' % (FZ, FZ))], 'oveq2d',
         '( y = %s -> ( N x. ( y ^ ( N - 1 ) ) ) = ( N x. ( %s ^ ( N - 1 ) ) ) )' % (FZ, FZ))
RHS = '( ( N x. ( %s ^ ( N - 1 ) ) ) x. %s )' % (FZ, DFZ)
dvc = w.s([ce1, ce2, fzc, dfzc, ync, ynm, dvm, dex, se, sf], 'dvmptco',
          '( %s -> ( CC _D %s ) = %s )' % (A0, MPN, MP('z', 'D', RHS)))
nca1 = w.s([w.s([nn], 'adantr', '( %s -> N e. NN )' % A1)], 'nncnd', '( %s -> N e. CC )' % A1)
nm11 = w.s([w.s([nn], 'adantr', '( %s -> N e. NN )' % A1), w.inst('nnm1nn0')], 'syl', '( %s -> ( N - 1 ) e. NN0 )' % A1)
rhsc = w.s([w.s([nca1, w.s([fzc, nm11], 'expcld', '( %s -> ( %s ^ ( N - 1 ) ) e. CC )' % (A1, FZ))], 'mulcld',
                '( %s -> ( N x. ( %s ^ ( N - 1 ) ) ) e. CC )' % (A1, FZ)), dfzc], 'mulcld', '( %s -> %s e. CC )' % (A1, RHS))
ds = dvdom(w, A0, MPN, 'z', 'D', RHS, dvc, rhsc)
w.qed([cnc, ds], 'jca', '( %s -> %s )' % (A0, HOLG(MPN))); run1(w)

# ---- holmul ----------------------------------------------------------------
w = W('holmul', 'A pointwise product of two functions holomorphic on a common domain is holomorphic there.')
A0 = '( %s /\\ %s )' % (HOL, HOLG('G'))
A1 = '( %s /\\ z e. D )' % A0
MPM = MP('z', 'D', '( %s x. %s )' % (FZ, GZ))
hf = w.s([], 'simpl', '( %s -> %s )' % (A0, HOL))
hg = w.s([], 'simpr', '( %s -> %s )' % (A0, HOLG('G')))
fcn, dd, dcc, ff, fmpt, dvmF, dvfF = holctx(w, A0, hf, 'F')
gcn, ddg, dccg, gf, gmpt, dvmG, dvfG = holctx(w, A0, hg, 'G')
fmp = w.s([fmpt, fcn], 'eqeltrrd', '( %s -> %s e. ( D -cn-> CC ) )' % (A0, MP('z', 'D', FZ)))
gmp = w.s([gmpt, gcn], 'eqeltrrd', '( %s -> %s e. ( D -cn-> CC ) )' % (A0, MP('z', 'D', GZ)))
ej = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
mcn = w.s([w.s([ej], 'mulcn', 'x. e. ( ( %s tX %s ) Cn %s )' % (TOP, TOP, TOP))], 'a1i',
          '( %s -> x. e. ( ( %s tX %s ) Cn %s ) )' % (A0, TOP, TOP, TOP))
cnc = w.s([ej, mcn, fmp, gmp], 'cncfmpt2f', '( %s -> %s e. ( D -cn-> CC ) )' % (A0, MPM))
ce = cnel(w, A0)
zD = w.s([], 'simpr', '( %s -> z e. D )' % A1)
fzc = w.s([w.s([ff], 'adantr', '( %s -> F : D --> CC )' % A1), zD], 'ffvelcdmd', '( %s -> %s e. CC )' % (A1, FZ))
gzc = w.s([w.s([gf], 'adantr', '( %s -> G : D --> CC )' % A1), zD], 'ffvelcdmd', '( %s -> %s e. CC )' % (A1, GZ))
dfzc = w.s([w.s([dvfF], 'adantr', '( %s -> %s : D --> CC )' % (A1, DVF)), zD], 'ffvelcdmd', '( %s -> %s e. CC )' % (A1, DFZ))
dgzc = w.s([w.s([dvfG], 'adantr', '( %s -> %s : D --> CC )' % (A1, DVG)), zD], 'ffvelcdmd', '( %s -> %s e. CC )' % (A1, DGZ))
RHS = '( ( %s x. %s ) + ( %s x. %s ) )' % (DFZ, GZ, DGZ, FZ)
dvc = w.s([ce, fzc, dfzc, dvmF, gzc, dgzc, dvmG], 'dvmptmul', '( %s -> ( CC _D %s ) = %s )' % (A0, MPM, MP('z', 'D', RHS)))
rhsc = w.s([w.s([dfzc, gzc], 'mulcld', '( %s -> ( %s x. %s ) e. CC )' % (A1, DFZ, GZ)),
            w.s([dgzc, fzc], 'mulcld', '( %s -> ( %s x. %s ) e. CC )' % (A1, DGZ, FZ))], 'addcld',
           '( %s -> %s e. CC )' % (A1, RHS))
ds = dvdom(w, A0, MPM, 'z', 'D', RHS, dvc, rhsc)
w.qed([cnc, ds], 'jca', '( %s -> %s )' % (A0, HOLG(MPM))); run1(w)

# ---- holdiv ----------------------------------------------------------------
w = W('holdiv', 'A pointwise quotient of two functions holomorphic on a common domain, with nonvanishing denominator, is holomorphic there.')
NZ = 'A. v e. D ( G ` v ) =/= 0'
A0 = '( %s /\\ %s /\\ %s )' % (HOL, HOLG('G'), NZ)
A1 = '( %s /\\ z e. D )' % A0
MPD = MP('z', 'D', '( %s / %s )' % (FZ, GZ))
C0 = '( CC \\ { 0 } )'
hf = w.s([], 'simp1', '( %s -> %s )' % (A0, HOL))
hg = w.s([], 'simp2', '( %s -> %s )' % (A0, HOLG('G')))
nz = w.s([], 'simp3', '( %s -> %s )' % (A0, NZ))
fcn, dd, dcc, ff, fmpt, dvmF, dvfF = holctx(w, A0, hf, 'F')
gcn, ddg, dccg, gf, gmpt, dvmG, dvfG = holctx(w, A0, hg, 'G')
zD = w.s([], 'simpr', '( %s -> z e. D )' % A1)
fzc = w.s([w.s([ff], 'adantr', '( %s -> F : D --> CC )' % A1), zD], 'ffvelcdmd', '( %s -> %s e. CC )' % (A1, FZ))
gzc = w.s([w.s([gf], 'adantr', '( %s -> G : D --> CC )' % A1), zD], 'ffvelcdmd', '( %s -> %s e. CC )' % (A1, GZ))
dfzc = w.s([w.s([dvfF], 'adantr', '( %s -> %s : D --> CC )' % (A1, DVF)), zD], 'ffvelcdmd', '( %s -> %s e. CC )' % (A1, DFZ))
dgzc = w.s([w.s([dvfG], 'adantr', '( %s -> %s : D --> CC )' % (A1, DVG)), zD], 'ffvelcdmd', '( %s -> %s e. CC )' % (A1, DGZ))
sub = w.s([w.s([], 'fveq2', '( v = z -> ( G ` v ) = %s )' % GZ)], 'neeq1d', '( v = z -> ( ( G ` v ) =/= 0 <-> %s =/= 0 ) )' % GZ)
gzn = w.s([sub, w.s([nz], 'adantr', '( %s -> %s )' % (A1, NZ)), zD], 'rspcdva', '( %s -> %s =/= 0 )' % (A1, GZ))
gz0 = w.s([gzc, gzn, w.inst('eldifsn')], 'sylanbrc', '( %s -> %s e. %s )' % (A1, GZ, C0)) if False else w.s([w.s([gzc, gzn], 'jca', '( %s -> ( %s e. CC /\\ %s =/= 0 ) )' % (A1, GZ, GZ)), w.inst('eldifsn')], 'sylibr', '( %s -> %s e. %s )' % (A1, GZ, C0))
# continuity: ( F ` z ) x. ( 1 / ( G ` z ) )
fmp = w.s([fmpt, fcn], 'eqeltrrd', '( %s -> %s e. ( D -cn-> CC ) )' % (A0, MP('z', 'D', FZ)))
gmp = w.s([gmpt, gcn], 'eqeltrrd', '( %s -> %s e. ( D -cn-> CC ) )' % (A0, MP('z', 'D', GZ)))
c0cc = w.s([w.s([], 'difss', '%s C_ CC' % C0)], 'a1i', '( %s -> %s C_ CC )' % (A0, C0))
gmf = w.s([gz0, w.s([], 'eqid', '%s = %s' % (MP('z', 'D', GZ), MP('z', 'D', GZ)))], 'fmptd',
          '( %s -> %s : D --> %s )' % (A0, MP('z', 'D', GZ), C0))
gmp0 = w.s([gmf, w.s([c0cc, gmp, w.inst('cncfcdm')], 'syl2anc',
                     '( %s -> ( %s e. ( D -cn-> %s ) <-> %s : D --> %s ) )' % (A0, MP('z', 'D', GZ), C0, MP('z', 'D', GZ), C0))],
           'mpbird', '( %s -> %s e. ( D -cn-> %s ) )' % (A0, MP('z', 'D', GZ), C0))
INV = MP('x', C0, '( 1 / x )')
cdc = w.s([w.s([w.s([], '1cn', '1 e. CC'), w.s([], 'eqid', '%s = %s' % (INV, INV), name='e%d' % w.n)], 'cdivcncf' if False else 'ax-mp', 'dummy')], 'a1i', 'dummy2') if False else None
eqinv = w.s([], 'eqid', '%s = %s' % (INV, INV))
cdcn = w.s([eqinv], 'cdivcncf', '( 1 e. CC -> %s e. ( %s -cn-> CC ) )' % (INV, C0))
cdcnd = w.s([w.s([], '1cnd', '( %s -> 1 e. CC )' % A0), cdcn], 'syl', '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, INV, C0))
nfz = w.s([], 'nfv', 'F/ z %s' % A0)
c0ss = w.s([w.s([], 'ssid', '%s C_ %s' % (C0, C0))], 'a1i', '( %s -> %s C_ %s )' % (A0, C0, C0))
stx = w.s([], 'oveq2', '( x = %s -> ( 1 / x ) = ( 1 / %s ) )' % (GZ, GZ))
rcn = w.s([nfz, gmp0, cdcnd, c0ss, stx], 'cncfcompt2', '( %s -> %s e. ( D -cn-> CC ) )' % (A0, MP('z', 'D', '( 1 / %s )' % GZ)))
ej = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
mcn = w.s([w.s([ej], 'mulcn', 'x. e. ( ( %s tX %s ) Cn %s )' % (TOP, TOP, TOP))], 'a1i',
          '( %s -> x. e. ( ( %s tX %s ) Cn %s ) )' % (A0, TOP, TOP, TOP))
prd = w.s([ej, mcn, fmp, rcn], 'cncfmpt2f', '( %s -> %s e. ( D -cn-> CC ) )' % (A0, MP('z', 'D', '( %s x. ( 1 / %s ) )' % (FZ, GZ))))
dre = w.s([w.s([fzc, gzc, gzn], 'divrecd', '( %s -> ( %s / %s ) = ( %s x. ( 1 / %s ) ) )' % (A1, FZ, GZ, FZ, GZ))], 'mpteq2dva',
          '( %s -> %s = %s )' % (A0, MPD, MP('z', 'D', '( %s x. ( 1 / %s ) )' % (FZ, GZ))))
cnc = w.s([dre, prd], 'eqeltrd', '( %s -> %s e. ( D -cn-> CC ) )' % (A0, MPD))
ce = cnel(w, A0)
RHS = '( ( ( %s x. %s ) - ( %s x. %s ) ) / ( %s ^ 2 ) )' % (DFZ, GZ, DGZ, FZ, GZ)
dvc = w.s([ce, fzc, dfzc, dvmF, gz0, dgzc, dvmG], 'dvmptdiv', '( %s -> ( CC _D %s ) = %s )' % (A0, MPD, MP('z', 'D', RHS)))
g2n = w.s([gzc, gzn, w.s([w.s([], '2z', '2 e. ZZ')], 'a1i', '( %s -> 2 e. ZZ )' % A1)], 'expne0d', '( %s -> ( %s ^ 2 ) =/= 0 )' % (A1, GZ))
rhsc = w.s([w.s([w.s([dfzc, gzc], 'mulcld', '( %s -> ( %s x. %s ) e. CC )' % (A1, DFZ, GZ)),
                 w.s([dgzc, fzc], 'mulcld', '( %s -> ( %s x. %s ) e. CC )' % (A1, DGZ, FZ))], 'subcld',
                '( %s -> ( ( %s x. %s ) - ( %s x. %s ) ) e. CC )' % (A1, DFZ, GZ, DGZ, FZ)),
            w.s([gzc], 'sqcld', '( %s -> ( %s ^ 2 ) e. CC )' % (A1, GZ)), g2n], 'divcld', '( %s -> %s e. CC )' % (A1, RHS))
ds = dvdom(w, A0, MPD, 'z', 'D', RHS, dvc, rhsc)
w.qed([cnc, ds], 'jca', '( %s -> %s )' % (A0, HOLG(MPD))); run1(w)
