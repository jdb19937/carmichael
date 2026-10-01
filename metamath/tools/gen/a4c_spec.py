"""Sortie A4c, batch 16: the round argument for the extraction loop
(Lean: AlgExtract.extractGo_spec, extract_spec)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from a4clib import *
import lin

only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

VEBK = 'A. w e. ~P ran O ( ( # ` w ) = B -> E. s e. ~P w ( s =/= (/) /\\ L || ( prod_ q e. s q - 1 ) ) )'
ESO = ('( ( L e. NN /\\ 2 <_ L ) /\\ ( N e. NN0 /\\ X e. NN0 /\\ B e. NN ) /\\ '
       '( O e. Word NN0 /\\ A. p e. ran O ( 2 <_ p /\\ p <_ X ) /\\ %s ) )' % VEBK)
OC = '( O e. Word NN0 /\\ A. p e. ran O ( 2 <_ p /\\ p <_ X ) )'
LG = '( ( L + 1 ) Nlog N )'

def EG(y, m, u, t): return '( ( ( ( ( L ExtractGo N ) ` %s ) ` %s ) ` %s ) ` %s )' % (y, m, u, t)
def F1(x): return '( 1st ` %s )' % x
def MMe(x): return '( 1st ` ( 2nd ` %s ) )' % F1(x)
def SSe(x): return '( 2nd ` ( 2nd ` %s ) )' % F1(x)
def WC(y): return "( Fun `' %s /\\ ran %s C_ ran O )" % (y, y)
def IU(y, u): return "( Fun `' %s /\\ ran %s C_ ran O /\\ ( ran %s i^i ran %s ) = (/) )" % (u, u, u, y)
def IE(y, u, e):
    return ("( ( Fun `' %s /\\ ran %s C_ ran O ) /\\ ( ( ran %s i^i ran %s ) = (/) /\\ ( ran %s i^i ran %s ) = (/) ) )"
            % (e, e, e, y, e, u))
def IM(m, u): return '( %s = %s /\\ L || ( %s - 1 ) /\\ %s <_ N )' % (m, PRD(u), m, m)
def IT(t, e): return '( %s /\\ %s /\\ ( # ` %s ) < B )' % (TS('L', t, e), TC('L', t, e), e)
def SUPX(y, e, h): return '( ( %s + 1 ) x. B ) <_ ( ( ( # ` %s ) + ( %s x. B ) ) + ( # ` %s ) )' % (LG, y, h, e)
def IHc(y, m, e, h): return '( ( ( L + 1 ) ^ %s ) <_ %s /\\ %s )' % (h, m, SUPX(y, e, h))
def INV(y, m, u, e, t, h):
    return '( ( %s /\\ %s ) /\\ ( %s /\\ %s ) /\\ %s )' % (IU(y, u), IE(y, u, e), IM(m, u), IT(t, e), IHc(y, m, e, h))
def OUTC(y, m, u, t):
    E = EG(y, m, u, t); MM = MMe(E); SS = SSe(E)
    return ("( %s =/= %s /\\ ( Fun `' %s /\\ ran %s C_ ran O /\\ %s = %s ) /\\ "
            "( L || ( %s - 1 ) /\\ N < %s /\\ %s <_ ( N x. ( X ^ B ) ) ) )"
            % (F1(E), NONE, SS, SS, PRD(SS), MM, MM, MM, MM))

QU = [('m', 'NN0'), ('u', 'Word NN0'), ('e', 'Word NN0'), ('t', 'Tbl'), ('h', 'NN0')]
BODY = '( ( %s /\\ %s ) -> %s )' % (WC('y'), INV('y', 'm', 'u', 'e', 't', 'h'), OUTC('y', 'm', 'u', 't'))
CSV = '( <" P "> ++ V )'

def esoparts(w, A, out):
    ll = w.s([w.s([out], 'simp1d', '( %s -> ( L e. NN /\\ 2 <_ L ) )' % A)], 'simpld', '( %s -> L e. NN )' % A)
    l2 = w.s([w.s([out], 'simp1d', '( %s -> ( L e. NN /\\ 2 <_ L ) )' % A)], 'simprd', '( %s -> 2 <_ L )' % A)
    nn = w.s([w.s([out], 'simp2d', '( %s -> ( N e. NN0 /\\ X e. NN0 /\\ B e. NN ) )' % A)], 'simp1d', '( %s -> N e. NN0 )' % A)
    xx = w.s([w.s([out], 'simp2d', '( %s -> ( N e. NN0 /\\ X e. NN0 /\\ B e. NN ) )' % A)], 'simp2d', '( %s -> X e. NN0 )' % A)
    bb = w.s([w.s([out], 'simp2d', '( %s -> ( N e. NN0 /\\ X e. NN0 /\\ B e. NN ) )' % A)], 'simp3d', '( %s -> B e. NN )' % A)
    oo = w.s([w.s([out], 'simp3d', '( %s -> ( O e. Word NN0 /\\ A. p e. ran O ( 2 <_ p /\\ p <_ X ) /\\ %s ) )' % (A, VEBK))],
             'simp1d', '( %s -> O e. Word NN0 )' % A)
    op = w.s([w.s([out], 'simp3d', '( %s -> ( O e. Word NN0 /\\ A. p e. ran O ( 2 <_ p /\\ p <_ X ) /\\ %s ) )' % (A, VEBK))],
             'simp2d', '( %s -> A. p e. ran O ( 2 <_ p /\\ p <_ X ) )' % A)
    vb = w.s([w.s([out], 'simp3d', '( %s -> ( O e. Word NN0 /\\ A. p e. ran O ( 2 <_ p /\\ p <_ X ) /\\ %s ) )' % (A, VEBK))],
             'simp3d', '( %s -> %s )' % (A, VEBK))
    return ll, l2, nn, xx, bb, oo, op, vb

def _b(w, ctx, goal):
    A = ctx.A
    U = '( %s /\\ ( %s /\\ %s ) )' % (A, WC('(/)'), INV('(/)', 'm', 'u', 'e', 't', 'h'))
    up = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (U, f))
    ll, l2, nn, xx, bb, oo, op, vb = esoparts(w, U, up(ctx.out, ESO))
    mm = up(ctx.v[0], 'm e. NN0'); ee = up(ctx.v[2], 'e e. Word NN0'); hh = up(ctx.v[4], 'h e. NN0')
    inv = w.s([w.s([], 'simpr', '( %s -> ( %s /\\ %s ) )' % (U, WC('(/)'), INV('(/)', 'm', 'u', 'e', 't', 'h')))], 'simprd',
              '( %s -> %s )' % (U, INV('(/)', 'm', 'u', 'e', 't', 'h')))
    i2 = w.s([inv], 'simp2d', '( %s -> ( %s /\\ %s ) )' % (U, IM('m', 'u'), IT('t', 'e')))
    i3 = w.s([inv], 'simp3d', '( %s -> %s )' % (U, IHc('(/)', 'm', 'e', 'h')))
    mle = w.s([w.s([i2], 'simpld', '( %s -> %s )' % (U, IM('m', 'u')))], 'simp3d', '( %s -> m <_ N )' % U)
    elt = w.s([w.s([i2], 'simprd', '( %s -> %s )' % (U, IT('t', 'e')))], 'simp3d', '( %s -> ( # ` e ) < B )' % U)
    pwle = w.s([i3], 'simpld', '( %s -> ( ( L + 1 ) ^ h ) <_ m )' % U)
    sup = w.s([i3], 'simprd', '( %s -> %s )' % (U, SUPX('(/)', 'e', 'h')))
    h0 = w.s([w.s([w.s([], 'hash0', '( # ` (/) ) = 0')], 'a1i', '( %s -> ( # ` (/) ) = 0 )' % U)], 'oveq1d',
             '( %s -> ( ( # ` (/) ) + ( h x. B ) ) = ( 0 + ( h x. B ) ) )' % U)
    h0b = w.s([h0], 'oveq1d',
              '( %s -> ( ( ( # ` (/) ) + ( h x. B ) ) + ( # ` e ) ) = ( ( 0 + ( h x. B ) ) + ( # ` e ) ) )' % U)
    SUP0 = '( ( %s + 1 ) x. B ) <_ ( ( 0 + ( h x. B ) ) + ( # ` e ) )' % LG
    sup0 = w.s([sup, h0b], 'breqtrd', '( %s -> %s )' % (U, SUP0))
    lcl = w.s([ee, w.inst('lencl')], 'syl', '( %s -> ( # ` e ) e. NN0 )' % U)
    HYP = '( ( ( ( ( L + 1 ) ^ h ) <_ m /\\ m <_ N ) /\\ ( # ` e ) < B ) /\\ %s )' % SUP0
    hyp = w.s([w.s([w.s([pwle, mle], 'jca', '( %s -> ( ( ( L + 1 ) ^ h ) <_ m /\\ m <_ N ) )' % U), elt], 'jca',
                   '( %s -> ( ( ( ( L + 1 ) ^ h ) <_ m /\\ m <_ N ) /\\ ( # ` e ) < B ) )' % U), sup0], 'jca',
              '( %s -> %s )' % (U, HYP))
    nhyp = w.s([w.s([w.s([ll, l2], 'jca', '( %s -> ( L e. NN /\\ 2 <_ L ) )' % U),
                     w.s([nn, bb], 'jca', '( %s -> ( N e. NN0 /\\ B e. NN ) )' % U),
                     w.s([mm, hh, lcl], '3jca', '( %s -> ( m e. NN0 /\\ h e. NN0 /\\ ( # ` e ) e. NN0 ) )' % U)], '3jca',
                    '( %s -> ( ( L e. NN /\\ 2 <_ L ) /\\ ( N e. NN0 /\\ B e. NN ) /\\ ( m e. NN0 /\\ h e. NN0 /\\ ( # ` e ) e. NN0 ) ) )' % U),
                w.inst('extgol1')], 'syl', '( %s -> -. %s )' % (U, HYP))
    return w.s([w.s([hyp, nhyp], 'pm2.21dd', '( %s -> %s )' % (U, OUTC('(/)', 'm', 'u', 't')))], 'ex',
               '( %s -> %s )' % (A, goal))

# ------------------------------------------------------------------ disjnel
if not only or 'disjnel' in only:
    w = W('disjnel', 'An element of one of two disjoint sets is outside the other.')
    A = '( ( A i^i C ) = (/) /\\ P e. C )'
    B = '( %s /\\ P e. A )' % A
    inb = w.s([w.s([w.s([], 'simpr', '( %s -> P e. A )' % B),
                    w.s([w.s([], 'simpr', '( %s -> P e. C )' % A)], 'adantr', '( %s -> P e. C )' % B)], 'jca',
                   '( %s -> ( P e. A /\\ P e. C ) )' % B),
               w.s([w.s([], 'elin', '( P e. ( A i^i C ) <-> ( P e. A /\\ P e. C ) )')], 'a1i',
                   '( %s -> ( P e. ( A i^i C ) <-> ( P e. A /\\ P e. C ) ) )' % B)], 'mpbird',
              '( %s -> P e. ( A i^i C ) )' % B)
    inz = w.s([inb, w.s([w.s([], 'simpl', '( %s -> ( A i^i C ) = (/) )' % A)], 'adantr',
                        '( %s -> ( A i^i C ) = (/) )' % B)], 'eleqtrd', '( %s -> P e. (/) )' % B)
    w.qed([inz, w.s([w.s([], 'noel', '-. P e. (/)')], 'a1i', '( %s -> -. P e. (/) )' % B)], 'pm2.65da',
          '( %s -> -. P e. A )' % A)
    run(w)

def outtrans(w, ante, old4, new4, eqstep):
    """( ante -> ( OUTC( old ) <-> OUTC( new ) ) ) from the equality of the results"""
    OLD = F1(EG(*old4)); NEW = F1(EG(*new4))
    E = '%s = %s' % (OLD, NEW)
    idst = w.s([], 'id', '( %s -> %s )' % (E, E))
    oSS = '( 2nd ` ( 2nd ` %s ) )' % OLD
    nSS = '( 2nd ` ( 2nd ` %s ) )' % NEW
    s1 = w.s([idst], 'fveq2d', '( %s -> ( 2nd ` %s ) = ( 2nd ` %s ) )' % (E, OLD, NEW))
    s2 = w.s([s1], 'fveq2d', '( %s -> %s = %s )' % (E, oSS, nSS))
    rules = {OLD: (NEW, idst), PRD(oSS): (PRD(nSS), prdeq(w, E, oSS, nSS, s2))}
    st, ne = w.wcongr(OUTC(*old4), {}, E, {}, rules=rules)
    assert ne == OUTC(*new4), 'outtrans mismatch:\n%s\n%s' % (ne, OUTC(*new4))
    return w.s([eqstep, st], 'syl', '( %s -> ( %s <-> %s ) )' % (ante, OUTC(*old4), OUTC(*new4)))

def eqants(w, ante, mv, uv, tv, cond, lab, rhs):
    """the antecedent of extractgocsn / extractgocss and the value it gives"""
    pass

def _s(w, ctx, goal):
    A = ctx.A
    CSE = '( <" P "> ++ e )'
    DSP = '( ( L DpStep P ) ` t )'
    DS1 = '( 1st ` %s )' % DSP
    HITV = '( %s ` ( 1 mod L ) )' % DS1
    SW = '( 2nd ` %s )' % HITV
    PS = '( 1st ` ( ProdL ` %s ) )' % SW
    MPv = '( m x. %s )' % PS
    SU = '( %s ++ u )' % SW
    HY = '( %s /\\ %s )' % (WC(CSV), INV(CSV, 'm', 'u', 'e', 't', 'h'))
    U = '( %s /\\ %s )' % (A, HY)
    up = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (U, f))
    out = up(ctx.out, ESO); ih = up(ctx.ih, ctx.ihf)
    vv = up(ctx.wrd, 'V e. Word NN0'); pp = up(ctx.let, 'P e. NN0')
    mm = up(ctx.v[0], 'm e. NN0'); uu = up(ctx.v[1], 'u e. Word NN0'); ee = up(ctx.v[2], 'e e. Word NN0')
    tt = up(ctx.v[3], 't e. Tbl'); hh = up(ctx.v[4], 'h e. NN0')
    ll, l2, nn, xx, bb, oo, op, vb = esoparts(w, U, out)
    hy = w.s([], 'simpr', '( %s -> %s )' % (U, HY))
    wcc = w.s([hy], 'simpld', '( %s -> %s )' % (U, WC(CSV)))
    inv = w.s([hy], 'simprd', '( %s -> %s )' % (U, INV(CSV, 'm', 'u', 'e', 't', 'h')))
    fucsv = w.s([wcc], 'simpld', "( %s -> Fun `' %s )" % (U, CSV))
    rncsvO = w.s([wcc], 'simprd', '( %s -> ran %s C_ ran O )' % (U, CSV))
    i1 = w.s([inv], 'simp1d', '( %s -> ( %s /\\ %s ) )' % (U, IU(CSV, 'u'), IE(CSV, 'u', 'e')))
    i2 = w.s([inv], 'simp2d', '( %s -> ( %s /\\ %s ) )' % (U, IM('m', 'u'), IT('t', 'e')))
    i3 = w.s([inv], 'simp3d', '( %s -> %s )' % (U, IHc(CSV, 'm', 'e', 'h')))
    iu = w.s([i1], 'simpld', '( %s -> %s )' % (U, IU(CSV, 'u')))
    ie = w.s([i1], 'simprd', '( %s -> %s )' % (U, IE(CSV, 'u', 'e')))
    im = w.s([i2], 'simpld', '( %s -> %s )' % (U, IM('m', 'u')))
    it = w.s([i2], 'simprd', '( %s -> %s )' % (U, IT('t', 'e')))
    fuu = w.s([iu], 'simp1d', "( %s -> Fun `' u )" % U)
    rnuO = w.s([iu], 'simp2d', '( %s -> ran u C_ ran O )' % U)
    ducsv = w.s([iu], 'simp3d', '( %s -> ( ran u i^i ran %s ) = (/) )' % (U, CSV))
    fue = w.s([w.s([ie], 'simpld', "( %s -> ( Fun `' e /\\ ran e C_ ran O ) )" % U)], 'simpld', "( %s -> Fun `' e )" % U)
    rneO = w.s([w.s([ie], 'simpld', "( %s -> ( Fun `' e /\\ ran e C_ ran O ) )" % U)], 'simprd',
               '( %s -> ran e C_ ran O )' % U)
    decsv = w.s([w.s([ie], 'simprd', '( %s -> ( ( ran e i^i ran %s ) = (/) /\\ ( ran e i^i ran u ) = (/) ) )' % (U, CSV))],
                'simpld', '( %s -> ( ran e i^i ran %s ) = (/) )' % (U, CSV))
    deu = w.s([w.s([ie], 'simprd', '( %s -> ( ( ran e i^i ran %s ) = (/) /\\ ( ran e i^i ran u ) = (/) ) )' % (U, CSV))],
              'simprd', '( %s -> ( ran e i^i ran u ) = (/) )' % U)
    mpr = w.s([im], 'simp1d', '( %s -> m = %s )' % (U, PRD('u')))
    mdv = w.s([im], 'simp2d', '( %s -> L || ( m - 1 ) )' % U)
    mle = w.s([im], 'simp3d', '( %s -> m <_ N )' % U)
    tse = w.s([it], 'simp1d', '( %s -> %s )' % (U, TS('L', 't', 'e')))
    tce = w.s([it], 'simp2d', '( %s -> %s )' % (U, TC('L', 't', 'e')))
    elt = w.s([it], 'simp3d', '( %s -> ( # ` e ) < B )' % U)
    pwle = w.s([i3], 'simpld', '( %s -> ( ( L + 1 ) ^ h ) <_ m )' % U)
    sup = w.s([i3], 'simprd', '( %s -> %s )' % (U, SUPX(CSV, 'e', 'h')))
    # ---------------------------------------------------- the pool cons
    rncs = w.s([pp, vv, w.inst('algrncs')], 'syl2anc', '( %s -> ran %s = ( { P } u. ran V ) )' % (U, CSV))
    pex = w.s([pp], 'elexd', '( %s -> P e. _V )' % U)
    psn = w.s([pex, w.inst('snidg')], 'syl', '( %s -> P e. { P } )' % U)
    pcsv = w.s([w.s([psn, w.s([w.s([], 'ssun1', '{ P } C_ ( { P } u. ran V )')], 'a1i',
                              '( %s -> { P } C_ ( { P } u. ran V ) )' % U)], 'sseldd',
                    '( %s -> P e. ( { P } u. ran V ) )' % U),
                w.s([rncs], 'eqcomd', '( %s -> ( { P } u. ran V ) = ran %s )' % (U, CSV))], 'eleqtrd',
               '( %s -> P e. ran %s )' % (U, CSV))
    rnvss = w.s([w.s([w.s([], 'ssun2', 'ran V C_ ( { P } u. ran V )')], 'a1i',
                     '( %s -> ran V C_ ( { P } u. ran V ) )' % U),
                 w.s([rncs], 'eqcomd', '( %s -> ( { P } u. ran V ) = ran %s )' % (U, CSV))], 'sseqtrd',
                '( %s -> ran V C_ ran %s )' % (U, CSV))
    ndcs = w.s([pp, vv, w.inst('algndpcs')], 'syl2anc',
               "( %s -> ( Fun `' %s <-> ( -. P e. ran V /\\ Fun `' V ) ) )" % (U, CSV))
    nds = w.s([fucsv, ndcs], 'mpbid', "( %s -> ( -. P e. ran V /\\ Fun `' V ) )" % U)
    pnv = w.s([nds], 'simpld', '( %s -> -. P e. ran V )' % U)
    fuv = w.s([nds], 'simprd', "( %s -> Fun `' V )" % U)
    rnvO = w.s([rnvss, rncsvO], 'sstrd', '( %s -> ran V C_ ran O )' % U)
    wcv = w.s([fuv, rnvO], 'jca', '( %s -> %s )' % (U, WC('V')))
    pO = w.s([pcsv, rncsvO], 'sseldd', '( %s -> P e. ran O )' % U)
    # disjointness with V
    dcsvu = w.s([w.s([w.s([], 'incom', '( ran %s i^i ran u ) = ( ran u i^i ran %s )' % (CSV, CSV))], 'a1i',
                     '( %s -> ( ran %s i^i ran u ) = ( ran u i^i ran %s ) )' % (U, CSV, CSV)), ducsv], 'eqtrd',
                '( %s -> ( ran %s i^i ran u ) = (/) )' % (U, CSV))
    dvu = w.s([w.s([rnvss, dcsvu], 'jca', '( %s -> ( ran V C_ ran %s /\\ ( ran %s i^i ran u ) = (/) ) )' % (U, CSV, CSV)),
               w.inst('ssdisj')], 'syl', '( %s -> ( ran V i^i ran u ) = (/) )' % U)
    duv = w.s([w.s([w.s([], 'incom', '( ran u i^i ran V ) = ( ran V i^i ran u )')], 'a1i',
                   '( %s -> ( ran u i^i ran V ) = ( ran V i^i ran u ) )' % U), dvu], 'eqtrd',
              '( %s -> ( ran u i^i ran V ) = (/) )' % U)
    dev = w.s([w.s([rnvss, w.s([w.s([w.s([], 'incom', '( ran %s i^i ran e ) = ( ran e i^i ran %s )' % (CSV, CSV))], 'a1i',
                                    '( %s -> ( ran %s i^i ran e ) = ( ran e i^i ran %s ) )' % (U, CSV, CSV)), decsv], 'eqtrd',
                               '( %s -> ( ran %s i^i ran e ) = (/) )' % (U, CSV))], 'jca',
                   '( %s -> ( ran V C_ ran %s /\\ ( ran %s i^i ran e ) = (/) ) )' % (U, CSV, CSV)), w.inst('ssdisj')], 'syl',
              '( %s -> ( ran V i^i ran e ) = (/) )' % U)
    devr = w.s([w.s([w.s([], 'incom', '( ran e i^i ran V ) = ( ran V i^i ran e )')], 'a1i',
                    '( %s -> ( ran e i^i ran V ) = ( ran V i^i ran e ) )' % U), dev], 'eqtrd',
               '( %s -> ( ran e i^i ran V ) = (/) )' % U)
    pnu = w.s([w.s([ducsv, pcsv], 'jca', '( %s -> ( ( ran u i^i ran %s ) = (/) /\\ P e. ran %s ) )' % (U, CSV, CSV)),
               w.inst('disjnel')], 'syl', '( %s -> -. P e. ran u )' % U)
    pne = w.s([w.s([decsv, pcsv], 'jca', '( %s -> ( ( ran e i^i ran %s ) = (/) /\\ P e. ran %s ) )' % (U, CSV, CSV)),
               w.inst('disjnel')], 'syl', '( %s -> -. P e. ran e )' % U)
    # ---------------------------------------------------- the processed list at the cons
    csew = w.s([w.s([pp, w.inst('s1cl')], 'syl', '( %s -> <" P "> e. Word NN0 )' % U), ee, w.inst('ccatcl')], 'syl2anc',
               '( %s -> %s e. Word NN0 )' % (U, CSE))
    rnce = w.s([pp, ee, w.inst('algrncs')], 'syl2anc', '( %s -> ran %s = ( { P } u. ran e ) )' % (U, CSE))
    fucse = w.s([w.s([pne, fue], 'jca', "( %s -> ( -. P e. ran e /\\ Fun `' e ) )" % U),
                 w.s([pp, ee, w.inst('algndpcs')], 'syl2anc',
                     "( %s -> ( Fun `' %s <-> ( -. P e. ran e /\\ Fun `' e ) ) )" % (U, CSE))], 'mpbird',
                "( %s -> Fun `' %s )" % (U, CSE))
    psO = w.s([pO], 'snssd', '( %s -> { P } C_ ran O )' % U)
    rnceO = w.s([rnce, w.s([w.s([psO, rneO], 'jca', '( %s -> ( { P } C_ ran O /\\ ran e C_ ran O ) )' % U),
                            w.s([w.s([], 'unss', '( ( { P } C_ ran O /\\ ran e C_ ran O ) <-> ( { P } u. ran e ) C_ ran O )')], 'a1i',
                                '( %s -> ( ( { P } C_ ran O /\\ ran e C_ ran O ) <-> ( { P } u. ran e ) C_ ran O ) )' % U)], 'mpbid',
                           '( %s -> ( { P } u. ran e ) C_ ran O )' % U)], 'eqsstrd',
                '( %s -> ran %s C_ ran O )' % (U, CSE))
    def disjun(w, ante, sst, dst, other, eqce):
        """( ante -> ( ran CSE i^i other ) = (/) ) from ( ante -> -. P e. other ) and ( ante -> ( ran e i^i other ) = (/) )"""
        d1 = w.s([sst, w.s([w.s([], 'disjsn', '( ( %s i^i { P } ) = (/) <-> -. P e. %s )' % (other, other))], 'a1i',
                           '( %s -> ( ( %s i^i { P } ) = (/) <-> -. P e. %s ) )' % (ante, other, other))], 'mpbird',
                 '( %s -> ( %s i^i { P } ) = (/) )' % (ante, other))
        d2 = w.s([w.s([w.s([], 'incom', '( { P } i^i %s ) = ( %s i^i { P } )' % (other, other))], 'a1i',
                      '( %s -> ( { P } i^i %s ) = ( %s i^i { P } ) )' % (ante, other, other)), d1], 'eqtrd',
                 '( %s -> ( { P } i^i %s ) = (/) )' % (ante, other))
        d3 = w.s([w.s([d2, dst], 'jca', '( %s -> ( ( { P } i^i %s ) = (/) /\\ ( ran e i^i %s ) = (/) ) )' % (ante, other, other)),
                  w.s([w.s([], 'undisj1', '( ( ( { P } i^i %s ) = (/) /\\ ( ran e i^i %s ) = (/) ) <-> ( ( { P } u. ran e ) i^i %s ) = (/) )'
                            % (other, other, other))], 'a1i',
                      '( %s -> ( ( ( { P } i^i %s ) = (/) /\\ ( ran e i^i %s ) = (/) ) <-> ( ( { P } u. ran e ) i^i %s ) = (/) ) )'
                      % (ante, other, other, other))], 'mpbid',
                 '( %s -> ( ( { P } u. ran e ) i^i %s ) = (/) )' % (ante, other))
        return w.s([w.s([eqce], 'ineq1d', '( %s -> ( ran %s i^i %s ) = ( ( { P } u. ran e ) i^i %s ) )' % (ante, CSE, other, other)),
                    d3], 'eqtrd', '( %s -> ( ran %s i^i %s ) = (/) )' % (ante, CSE, other))
    dcev = disjun(w, U, pnv, devr, 'ran V', rnce)
    dceu = disjun(w, U, pnu, deu, 'ran u', rnce)
    # ---------------------------------------------------- one DP step
    dpo3 = w.s([ll, pp, tt], '3jca', '( %s -> ( L e. NN /\\ P e. NN0 /\\ t e. Tbl ) )' % U)
    DPOt = '( ( L e. NN /\\ P e. NN0 ) /\\ t e. Tbl )'
    dpo = w.s([w.s([ll, pp], 'jca', '( %s -> ( L e. NN /\\ P e. NN0 ) )' % U), tt], 'jca', '( %s -> %s )' % (U, DPOt))
    tsc = w.s([w.s([dpo3, w.s([ee, pne], 'jca', '( %s -> ( e e. Word NN0 /\\ -. P e. ran e ) )' % U), tse], '3jca',
                   '( %s -> ( ( L e. NN /\\ P e. NN0 /\\ t e. Tbl ) /\\ ( e e. Word NN0 /\\ -. P e. ran e ) /\\ %s ) )' % (U, TS('L', 't', 'e'))),
               w.inst('tblsnds')], 'syl', '( %s -> %s )' % (U, TS('L', DS1, CSE)))
    tcc = w.s([w.s([dpo3, ee, tce], '3jca',
                   '( %s -> ( ( L e. NN /\\ P e. NN0 /\\ t e. Tbl ) /\\ e e. Word NN0 /\\ %s ) )' % (U, TC('L', 't', 'e'))),
               w.inst('tblcmps')], 'syl', '( %s -> %s )' % (U, TC('L', DS1, CSE)))
    ds1 = w.s([w.s([dpo, w.inst('dpstepcl')], 'syl', '( %s -> %s e. ( Tbl X. NN0 ) )' % (U, DSP)), w.inst('xp1st')], 'syl',
              '( %s -> %s e. Tbl )' % (U, DS1))
    # lengths
    lcsv = w.s([pp, vv, w.inst('alglencs')], 'syl2anc', '( %s -> ( # ` %s ) = ( ( # ` V ) + 1 ) )' % (U, CSV))
    lcse = w.s([pp, ee, w.inst('alglencs')], 'syl2anc', '( %s -> ( # ` %s ) = ( ( # ` e ) + 1 ) )' % (U, CSE))
    lenv = w.s([vv, w.inst('lencl')], 'syl', '( %s -> ( # ` V ) e. NN0 )' % U)
    lene = w.s([ee, w.inst('lencl')], 'syl', '( %s -> ( # ` e ) e. NN0 )' % U)
    lvr = w.s([lenv], 'nn0red', '( %s -> ( # ` V ) e. RR )' % U)
    ler = w.s([lene], 'nn0red', '( %s -> ( # ` e ) e. RR )' % U)
    br = w.s([bb], 'nnred', '( %s -> B e. RR )' % U)
    hbr = w.s([w.s([hh], 'nn0red', '( %s -> h e. RR )' % U), br], 'remulcld', '( %s -> ( h x. B ) e. RR )' % U)
    lgn = w.s([w.s([w.s([ll, w.inst('peano2nn')], 'syl', '( %s -> ( L + 1 ) e. NN )' % U)], 'nnnn0d',
                   '( %s -> ( L + 1 ) e. NN0 )' % U), nn, w.inst('nlogcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (U, LG))
    lgbr = w.s([w.s([w.s([lgn], 'nn0red', '( %s -> %s e. RR )' % (U, LG)), w.inst('peano2re')], 'syl',
                    '( %s -> ( %s + 1 ) e. RR )' % (U, LG)), br], 'remulcld', '( %s -> ( ( %s + 1 ) x. B ) e. RR )' % (U, LG))
    # rewrite the supply inequality at the cons
    supv = w.s([sup, w.s([w.s([lcsv], 'oveq1d',
                              '( %s -> ( ( # ` %s ) + ( h x. B ) ) = ( ( ( # ` V ) + 1 ) + ( h x. B ) ) )' % (U, CSV))], 'oveq1d',
                         '( %s -> ( ( ( # ` %s ) + ( h x. B ) ) + ( # ` e ) ) = ( ( ( ( # ` V ) + 1 ) + ( h x. B ) ) + ( # ` e ) ) )' % (U, CSV))],
               'breqtrd', '( %s -> ( ( %s + 1 ) x. B ) <_ ( ( ( ( # ` V ) + 1 ) + ( h x. B ) ) + ( # ` e ) ) )' % (U, LG))
    # ==================================================== the none branch
    NB = '( %s /\\ %s = %s )' % (U, HITV, NONE)
    nb = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (NB, f))
    hitz = w.s([], 'simpr', '( %s -> %s = %s )' % (NB, HITV, NONE))
    EGV = EG('V', 'm', 'u', DS1)
    llN = nb(ll, 'L e. NN'); nnN = nb(nn, 'N e. NN0'); mmN = nb(mm, 'm e. NN0'); uuN = nb(uu, 'u e. Word NN0')
    ttN = nb(tt, 't e. Tbl'); ppN = nb(pp, 'P e. NN0'); vvN = nb(vv, 'V e. Word NN0')
    ajn, _fn = lnest(w, NB, [(w.s([llN, nnN], 'jca', '( %s -> ( L e. NN /\\ N e. NN0 ) )' % NB), '( L e. NN /\\ N e. NN0 )'),
                             (mmN, 'm e. NN0'), (uuN, 'u e. Word NN0'), (ttN, 't e. Tbl'),
                             (ppN, 'P e. NN0'), (vvN, 'V e. Word NN0'), (hitz, '%s = %s' % (HITV, NONE))])
    valn = w.s([ajn, w.inst('extractgocsn')], 'syl',
               '( %s -> %s = <. %s , ( ( ( 2nd ` %s ) + ( 2nd ` %s ) ) + 1 ) >. )'
               % (NB, EG(CSV, 'm', 'u', 't'), F1(EGV), EGV, DSP))
    p1n = prj(w, NB, EG(CSV, 'm', 'u', 't'), valn, F1(EGV), '( ( ( 2nd ` %s ) + ( 2nd ` %s ) ) + 1 )' % (EGV, DSP), 1)
    # the batch is not yet full
    CB = '( %s /\\ ( # ` %s ) = B )' % (NB, CSE)
    cb = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (CB, f))
    l2b = w.s([cb(nb(ll, 'L e. NN'), 'L e. NN'), cb(nb(oo, 'O e. Word NN0'), 'O e. Word NN0'),
               cb(nb(vb, VEBK), VEBK)], '3jca',
              '( %s -> ( L e. NN /\\ O e. Word NN0 /\\ %s ) )' % (CB, VEBK))
    g3b = w.s([cb(nb(csew, '%s e. Word NN0' % CSE), '%s e. Word NN0' % CSE),
               cb(nb(fucse, "Fun `' %s" % CSE), "Fun `' %s" % CSE),
               w.s([], 'simpr', '( %s -> ( # ` %s ) = B )' % (CB, CSE))], '3jca',
              "( %s -> ( %s e. Word NN0 /\\ Fun `' %s /\\ ( # ` %s ) = B ) )" % (CB, CSE, CSE, CSE))
    vbc = w.s([w.s([w.s([l2b, g3b, cb(nb(rnceO, 'ran %s C_ ran O' % CSE), 'ran %s C_ ran O' % CSE)], '3jca',
                        "( %s -> ( ( L e. NN /\\ O e. Word NN0 /\\ %s ) /\\ ( %s e. Word NN0 /\\ Fun `' %s /\\ ( # ` %s ) = B ) /\\ ran %s C_ ran O ) )"
                        % (CB, VEBK, CSE, CSE, CSE, CSE)),
                    cb(nb(tcc, TC('L', DS1, CSE)), TC('L', DS1, CSE))], 'jca',
                   "( %s -> ( ( ( L e. NN /\\ O e. Word NN0 /\\ %s ) /\\ ( %s e. Word NN0 /\\ Fun `' %s /\\ ( # ` %s ) = B ) /\\ ran %s C_ ran O ) /\\ %s ) )"
                   % (CB, VEBK, CSE, CSE, CSE, CSE, TC('L', DS1, CSE))), w.inst('extgol2')], 'syl',
              '( %s -> %s =/= %s )' % (CB, HITV, NONE))
    nne = w.s([w.s([w.s([], 'nne', '( -. %s =/= %s <-> %s = %s )' % (HITV, NONE, HITV, NONE))], 'biimpri',
                   '( %s = %s -> -. %s =/= %s )' % (HITV, NONE, HITV, NONE))], 'a1i',
              '( %s -> ( %s = %s -> -. %s =/= %s ) )' % (CB, HITV, NONE, HITV, NONE))
    ncb = w.s([vbc, w.s([cb(hitz, '%s = %s' % (HITV, NONE)), nne], 'mpd', '( %s -> -. %s =/= %s )' % (CB, HITV, NONE))],
              'pm2.65da', '( %s -> -. ( # ` %s ) = B )' % (NB, CSE))
    lcer = w.s([w.s([nb(csew, '%s e. Word NN0' % CSE), w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (NB, CSE))],
               'nn0red', '( %s -> ( # ` %s ) e. RR )' % (NB, CSE))
    lez = w.s([nb(lene, '( # ` e ) e. NN0')], 'nn0zd', '( %s -> ( # ` e ) e. ZZ )' % NB)
    bz = w.s([w.s([nb(bb, 'B e. NN')], 'nnnn0d', '( %s -> B e. NN0 )' % NB)], 'nn0zd', '( %s -> B e. ZZ )' % NB)
    lep1 = w.s([w.s([w.s([lez, bz], 'jca', '( %s -> ( ( # ` e ) e. ZZ /\\ B e. ZZ ) )' % NB), w.inst('zltp1le')], 'syl',
                    '( %s -> ( ( # ` e ) < B <-> ( ( # ` e ) + 1 ) <_ B ) )' % NB), nb(elt, '( # ` e ) < B')], 'mpbid',
               '( %s -> ( ( # ` e ) + 1 ) <_ B )' % NB)
    lcele = w.s([nb(lcse, '( # ` %s ) = ( ( # ` e ) + 1 )' % CSE), lep1], 'eqbrtrd', '( %s -> ( # ` %s ) <_ B )' % (NB, CSE))
    lcelt = w.s([w.s([lcer, nb(br, 'B e. RR')], 'ltlend', '( %s -> ( ( # ` %s ) < B <-> ( ( # ` %s ) <_ B /\\ B =/= ( # ` %s ) ) ) )'
                     % (NB, CSE, CSE, CSE)),
                 w.s([lcele, w.s([w.s([ncb, w.inst('neqned')], 'syl', '( %s -> ( # ` %s ) =/= B )' % (NB, CSE))], 'necomd',
                                 '( %s -> B =/= ( # ` %s ) )' % (NB, CSE))], 'jca',
                     '( %s -> ( ( # ` %s ) <_ B /\\ B =/= ( # ` %s ) ) )' % (NB, CSE, CSE))], 'mpbird',
                '( %s -> ( # ` %s ) < B )' % (NB, CSE))
    # the supply inequality at ( V , CSE )
    cbe = w.s([w.s([w.s([nb(lgbr, '( ( %s + 1 ) x. B ) e. RR' % LG), nb(lvr, '( # ` V ) e. RR'),
                         nb(hbr, '( h x. B ) e. RR')], '3jca',
                        '( %s -> ( ( ( %s + 1 ) x. B ) e. RR /\\ ( # ` V ) e. RR /\\ ( h x. B ) e. RR ) )' % (NB, LG)),
                    w.s([nb(ler, '( # ` e ) e. RR'), nb(supv, '( ( %s + 1 ) x. B ) <_ ( ( ( ( # ` V ) + 1 ) + ( h x. B ) ) + ( # ` e ) )' % LG)],
                        'jca', '( %s -> ( ( # ` e ) e. RR /\\ ( ( %s + 1 ) x. B ) <_ ( ( ( ( # ` V ) + 1 ) + ( h x. B ) ) + ( # ` e ) ) ) )' % (NB, LG))],
                   'jca',
                   '( %s -> ( ( ( ( %s + 1 ) x. B ) e. RR /\\ ( # ` V ) e. RR /\\ ( h x. B ) e. RR ) /\\ ( ( # ` e ) e. RR /\\ ( ( %s + 1 ) x. B ) <_ ( ( ( ( # ` V ) + 1 ) + ( h x. B ) ) + ( # ` e ) ) ) ) )' % (NB, LG, LG)),
               w.inst('extgocbe')], 'syl',
              '( %s -> ( ( %s + 1 ) x. B ) <_ ( ( ( # ` V ) + ( h x. B ) ) + ( ( # ` e ) + 1 ) ) )' % (NB, LG))
    supn = w.s([cbe, w.s([w.s([nb(lcse, '( # ` %s ) = ( ( # ` e ) + 1 )' % CSE)], 'eqcomd',
                              '( %s -> ( ( # ` e ) + 1 ) = ( # ` %s ) )' % (NB, CSE))], 'oveq2d',
                         '( %s -> ( ( ( # ` V ) + ( h x. B ) ) + ( ( # ` e ) + 1 ) ) = ( ( ( # ` V ) + ( h x. B ) ) + ( # ` %s ) ) )' % (NB, CSE))],
               'breqtrd', '( %s -> %s )' % (NB, SUPX('V', CSE, 'h')))
    # the induction hypothesis at ( m , u , CSE , DS1 , h )
    invn = w.s([w.s([w.s([nb(fuu, "Fun `' u"), nb(rnuO, 'ran u C_ ran O'), nb(duv, '( ran u i^i ran V ) = (/)')], '3jca',
                         '( %s -> %s )' % (NB, IU('V', 'u'))),
                     w.s([w.s([nb(fucse, "Fun `' %s" % CSE), nb(rnceO, 'ran %s C_ ran O' % CSE)], 'jca',
                              "( %s -> ( Fun `' %s /\\ ran %s C_ ran O ) )" % (NB, CSE, CSE)),
                          w.s([nb(dcev, '( ran %s i^i ran V ) = (/)' % CSE), nb(dceu, '( ran %s i^i ran u ) = (/)' % CSE)], 'jca',
                              '( %s -> ( ( ran %s i^i ran V ) = (/) /\\ ( ran %s i^i ran u ) = (/) ) )' % (NB, CSE, CSE))], 'jca',
                         '( %s -> %s )' % (NB, IE('V', 'u', CSE)))], 'jca',
                    '( %s -> ( %s /\\ %s ) )' % (NB, IU('V', 'u'), IE('V', 'u', CSE))),
                w.s([w.s([nb(mpr, 'm = %s' % PRD('u')), nb(mdv, 'L || ( m - 1 )'), nb(mle, 'm <_ N')], '3jca',
                         '( %s -> %s )' % (NB, IM('m', 'u'))),
                     w.s([nb(tsc, TS('L', DS1, CSE)), nb(tcc, TC('L', DS1, CSE)), lcelt], '3jca',
                         '( %s -> %s )' % (NB, IT(DS1, CSE)))], 'jca',
                    '( %s -> ( %s /\\ %s ) )' % (NB, IM('m', 'u'), IT(DS1, CSE))),
                w.s([nb(pwle, '( ( L + 1 ) ^ h ) <_ m'), supn], 'jca', '( %s -> %s )' % (NB, IHc('V', 'm', CSE, 'h')))],
               '3jca', '( %s -> %s )' % (NB, INV('V', 'm', 'u', CSE, DS1, 'h')))
    r = ctx.rn
    ihb = subst(BODY, 'y', 'V')
    for i, nm in enumerate(['m', 'u', 'e', 't', 'h']):
        ihb = subst(ihb, nm, r[i])
    ihn, _ = instn(w, NB, nb(ih, ctx.ihf), [(r[0], 'NN0'), (r[1], 'Word NN0'), (r[2], 'Word NN0'), (r[3], 'Tbl'), (r[4], 'NN0')],
                   ihb, ['m', 'u', CSE, DS1, 'h'],
                   [nb(mm, 'm e. NN0'), nb(uu, 'u e. Word NN0'), nb(csew, '%s e. Word NN0' % CSE),
                    nb(ds1, '%s e. Tbl' % DS1), nb(hh, 'h e. NN0')])
    gotn = w.s([ihn, w.s([nb(wcv, WC('V')), invn], 'jca', '( %s -> ( %s /\\ %s ) )' % (NB, WC('V'), INV('V', 'm', 'u', CSE, DS1, 'h')))],
               'mpd', '( %s -> %s )' % (NB, OUTC('V', 'm', 'u', DS1)))
    trn = outtrans(w, NB, (CSV, 'm', 'u', 't'), ('V', 'm', 'u', DS1), p1n)
    gn = w.s([gotn, trn], 'mpbird', '( %s -> %s )' % (NB, OUTC(CSV, 'm', 'u', 't')))
    # ==================================================== the some branch
    SB = '( %s /\\ -. %s = %s )' % (U, HITV, NONE)
    sb = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (SB, f))
    hitne = w.s([w.s([], 'simpr', '( %s -> -. %s = %s )' % (SB, HITV, NONE)), w.inst('neqned')], 'syl',
                '( %s -> %s =/= %s )' % (SB, HITV, NONE))
    m1n = w.s([w.s([w.s([], '1z', '1 e. ZZ')], 'a1i', '( %s -> 1 e. ZZ )' % SB), sb(ll, 'L e. NN'), w.inst('zmodcl')], 'syl2anc',
              '( %s -> ( 1 mod L ) e. NN0 )' % SB)
    swc = w.s([w.s([w.s([sb(ds1, '%s e. Tbl' % DS1), m1n], 'jca', '( %s -> ( %s e. Tbl /\\ ( 1 mod L ) e. NN0 ) )' % (SB, DS1)),
                    hitne], 'jca', '( %s -> ( ( %s e. Tbl /\\ ( 1 mod L ) e. NN0 ) /\\ %s =/= %s ) )' % (SB, DS1, HITV, NONE)),
               w.inst('tblpay')], 'syl', '( %s -> ( %s e. Word NN0 /\\ %s = ( inl ` %s ) ) )' % (SB, SW, HITV, SW))
    sww = w.s([swc], 'simpld', '( %s -> %s e. Word NN0 )' % (SB, SW))
    tsi, _ = inst1(w, SB, sb(tsc, TS('L', DS1, CSE)), 'd', 'NN0',
                   TS('L', DS1, CSE)[len('A. d e. NN0 '):], '( 1 mod L )', m1n)
    tsg = w.s([tsi, hitne], 'mpd',
              "( %s -> ( ( %s =/= (/) /\\ Fun `' %s ) /\\ ( ran %s C_ ran %s /\\ ( %s mod L ) = ( 1 mod L ) ) ) )"
              % (SB, SW, SW, SW, CSE, PRD(SW)))
    swnz = w.s([w.s([tsg], 'simpld', "( %s -> ( %s =/= (/) /\\ Fun `' %s ) )" % (SB, SW, SW))], 'simpld',
               '( %s -> %s =/= (/) )' % (SB, SW))
    fusw = w.s([w.s([tsg], 'simpld', "( %s -> ( %s =/= (/) /\\ Fun `' %s ) )" % (SB, SW, SW))], 'simprd',
               "( %s -> Fun `' %s )" % (SB, SW))
    swce = w.s([w.s([tsg], 'simprd', '( %s -> ( ran %s C_ ran %s /\\ ( %s mod L ) = ( 1 mod L ) ) )' % (SB, SW, CSE, PRD(SW)))],
               'simpld', '( %s -> ran %s C_ ran %s )' % (SB, SW, CSE))
    swmod = w.s([w.s([tsg], 'simprd', '( %s -> ( ran %s C_ ran %s /\\ ( %s mod L ) = ( 1 mod L ) ) )' % (SB, SW, CSE, PRD(SW)))],
                'simprd', '( %s -> ( %s mod L ) = ( 1 mod L ) )' % (SB, PRD(SW)))
    swO = w.s([swce, sb(rnceO, 'ran %s C_ ran O' % CSE)], 'sstrd', '( %s -> ran %s C_ ran O )' % (SB, SW))
    qq = w.s([w.s([w.s([sb(oo, 'O e. Word NN0'), sb(op, 'A. p e. ran O ( 2 <_ p /\\ p <_ X )')], 'jca',
                       '( %s -> %s )' % (SB, OC)),
                   w.s([sww, swO], 'jca', '( %s -> ( %s e. Word NN0 /\\ ran %s C_ ran O ) )' % (SB, SW, SW))], 'jca',
                  '( %s -> ( %s /\\ ( %s e. Word NN0 /\\ ran %s C_ ran O ) ) )' % (SB, OC, SW, SW)), w.inst('extgoq')], 'syl',
              '( %s -> ( ( A. q e. ran %s 1 <_ q /\\ A. q e. ran %s 2 <_ q ) /\\ ( A. q e. ran %s q <_ X /\\ %s e. NN ) ) )'
              % (SB, SW, SW, SW, PRD(SW)))
    q1 = w.s([w.s([qq], 'simpld', '( %s -> ( A. q e. ran %s 1 <_ q /\\ A. q e. ran %s 2 <_ q ) )' % (SB, SW, SW))], 'simpld',
             '( %s -> A. q e. ran %s 1 <_ q )' % (SB, SW))
    q2 = w.s([w.s([qq], 'simpld', '( %s -> ( A. q e. ran %s 1 <_ q /\\ A. q e. ran %s 2 <_ q ) )' % (SB, SW, SW))], 'simprd',
             '( %s -> A. q e. ran %s 2 <_ q )' % (SB, SW))
    qx = w.s([w.s([qq], 'simprd', '( %s -> ( A. q e. ran %s q <_ X /\\ %s e. NN ) )' % (SB, SW, PRD(SW)))], 'simpld',
             '( %s -> A. q e. ran %s q <_ X )' % (SB, SW))
    prdn = w.s([w.s([qq], 'simprd', '( %s -> ( A. q e. ran %s q <_ X /\\ %s e. NN ) )' % (SB, SW, PRD(SW)))], 'simprd',
               '( %s -> %s e. NN )' % (SB, PRD(SW)))
    x1 = w.s([w.s([w.s([sww, swnz], 'jca', '( %s -> ( %s e. Word NN0 /\\ %s =/= (/) ) )' % (SB, SW, SW)),
                   w.s([q2, qx, sb(xx, 'X e. NN0')], '3jca',
                       '( %s -> ( A. q e. ran %s 2 <_ q /\\ A. q e. ran %s q <_ X /\\ X e. NN0 ) )' % (SB, SW, SW))], 'jca',
                  '( %s -> ( ( %s e. Word NN0 /\\ %s =/= (/) ) /\\ ( A. q e. ran %s 2 <_ q /\\ A. q e. ran %s q <_ X /\\ X e. NN0 ) ) )'
                  % (SB, SW, SW, SW, SW)), w.inst('extgox')], 'syl', '( %s -> 1 <_ X )' % SB)
    lswle = w.s([w.s([w.s([sww, sb(csew, '%s e. Word NN0' % CSE)], 'jca',
                          '( %s -> ( %s e. Word NN0 /\\ %s e. Word NN0 ) )' % (SB, SW, CSE)),
                      w.s([fusw, swce], 'jca', "( %s -> ( Fun `' %s /\\ ran %s C_ ran %s ) )" % (SB, SW, SW, CSE))], 'jca',
                     "( %s -> ( ( %s e. Word NN0 /\\ %s e. Word NN0 ) /\\ ( Fun `' %s /\\ ran %s C_ ran %s ) ) )" % (SB, SW, CSE, SW, SW, CSE)),
                 w.inst('algwrdss')], 'syl', '( %s -> ( # ` %s ) <_ ( # ` %s ) )' % (SB, SW, CSE))
    lezS = w.s([sb(lene, '( # ` e ) e. NN0')], 'nn0zd', '( %s -> ( # ` e ) e. ZZ )' % SB)
    bzS = w.s([w.s([sb(bb, 'B e. NN')], 'nnnn0d', '( %s -> B e. NN0 )' % SB)], 'nn0zd', '( %s -> B e. ZZ )' % SB)
    lep1S = w.s([w.s([w.s([lezS, bzS], 'jca', '( %s -> ( ( # ` e ) e. ZZ /\\ B e. ZZ ) )' % SB), w.inst('zltp1le')], 'syl',
                     '( %s -> ( ( # ` e ) < B <-> ( ( # ` e ) + 1 ) <_ B ) )' % SB), sb(elt, '( # ` e ) < B')], 'mpbid',
                '( %s -> ( ( # ` e ) + 1 ) <_ B )' % SB)
    lceleS = w.s([sb(lcse, '( # ` %s ) = ( ( # ` e ) + 1 )' % CSE), lep1S], 'eqbrtrd', '( %s -> ( # ` %s ) <_ B )' % (SB, CSE))
    lswr = w.s([w.s([sww, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (SB, SW))], 'nn0red',
               '( %s -> ( # ` %s ) e. RR )' % (SB, SW))
    lcerS = w.s([w.s([sb(csew, '%s e. Word NN0' % CSE), w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (SB, CSE))],
                'nn0red', '( %s -> ( # ` %s ) e. RR )' % (SB, CSE))
    lswB = lin.linarith(w, SB, [lswle, lceleS], '( # ` %s ) <_ B' % SW,
                        leaves={'( # ` %s )' % SW: lswr, '( # ` %s )' % CSE: lcerS, 'B': sb(br, 'B e. RR')})
    l4 = w.s([w.s([w.s([sb(xx, 'X e. NN0'), x1, w.s([sb(bb, 'B e. NN')], 'nnnn0d', '( %s -> B e. NN0 )' % SB)], '3jca',
                       '( %s -> ( X e. NN0 /\\ 1 <_ X /\\ B e. NN0 ) )' % SB),
                   w.s([sww, qx, lswB], '3jca',
                       '( %s -> ( %s e. Word NN0 /\\ A. q e. ran %s q <_ X /\\ ( # ` %s ) <_ B ) )' % (SB, SW, SW, SW))], 'jca',
                  '( %s -> ( ( X e. NN0 /\\ 1 <_ X /\\ B e. NN0 ) /\\ ( %s e. Word NN0 /\\ A. q e. ran %s q <_ X /\\ ( # ` %s ) <_ B ) ) )'
                  % (SB, SW, SW, SW)), w.inst('extgol4')], 'syl', '( %s -> %s <_ ( X ^ B ) )' % (SB, PRD(SW)))
    l3 = w.s([w.s([w.s([sb(ll, 'L e. NN'), sb(l2, '2 <_ L')], 'jca', '( %s -> ( L e. NN /\\ 2 <_ L ) )' % SB),
                   w.s([sww, swnz, q1], '3jca',
                       '( %s -> ( %s e. Word NN0 /\\ %s =/= (/) /\\ A. q e. ran %s 1 <_ q ) )' % (SB, SW, SW, SW)),
                   w.s([q2, swmod], 'jca', '( %s -> ( A. q e. ran %s 2 <_ q /\\ ( %s mod L ) = ( 1 mod L ) ) )' % (SB, SW, PRD(SW)))],
                  '3jca',
                  '( %s -> ( ( L e. NN /\\ 2 <_ L ) /\\ ( %s e. Word NN0 /\\ %s =/= (/) /\\ A. q e. ran %s 1 <_ q ) /\\ ( A. q e. ran %s 2 <_ q /\\ ( %s mod L ) = ( 1 mod L ) ) ) )'
                  % (SB, SW, SW, SW, SW, PRD(SW))), w.inst('extgol3')], 'syl',
             '( %s -> ( L || ( %s - 1 ) /\\ ( L + 1 ) <_ %s ) )' % (SB, PRD(SW), PRD(SW)))
    sdv = w.s([l3], 'simpld', '( %s -> L || ( %s - 1 ) )' % (SB, PRD(SW)))
    sge = w.s([l3], 'simprd', '( %s -> ( L + 1 ) <_ %s )' % (SB, PRD(SW)))
    pseq = w.s([sww, w.inst('prodlspec')], 'syl', '( %s -> %s = %s )' % (SB, PS, PRD(SW)))
    psn = w.s([pseq, w.s([prdn], 'nnnn0d', '( %s -> %s e. NN0 )' % (SB, PRD(SW)))], 'eqeltrd', '( %s -> %s e. NN0 )' % (SB, PS))
    mpn = w.s([sb(mm, 'm e. NN0'), psn], 'nn0mulcld', '( %s -> %s e. NN0 )' % (SB, MPv))
    suw = w.s([sww, sb(uu, 'u e. Word NN0'), w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word NN0 )' % (SB, SU))
    dsu = w.s([w.s([swce, sb(dceu, '( ran %s i^i ran u ) = (/)' % CSE)], 'jca',
                   '( %s -> ( ran %s C_ ran %s /\\ ( ran %s i^i ran u ) = (/) ) )' % (SB, SW, CSE, CSE)), w.inst('ssdisj')], 'syl',
              '( %s -> ( ran %s i^i ran u ) = (/) )' % (SB, SW))
    fusu = w.s([w.s([w.s([sww, sb(uu, 'u e. Word NN0')], 'jca', '( %s -> ( %s e. Word NN0 /\\ u e. Word NN0 ) )' % (SB, SW)),
                     w.s([w.s([fusw, sb(fuu, "Fun `' u")], 'jca', "( %s -> ( Fun `' %s /\\ Fun `' u ) )" % (SB, SW)), dsu], 'jca',
                         "( %s -> ( ( Fun `' %s /\\ Fun `' u ) /\\ ( ran %s i^i ran u ) = (/) ) )" % (SB, SW, SW))], 'jca',
                    "( %s -> ( ( %s e. Word NN0 /\\ u e. Word NN0 ) /\\ ( ( Fun `' %s /\\ Fun `' u ) /\\ ( ran %s i^i ran u ) = (/) ) ) )"
                    % (SB, SW, SW, SW)), w.inst('algndpccr')], 'syl', "( %s -> Fun `' %s )" % (SB, SU))
    rnsu = w.s([sww, sb(uu, 'u e. Word NN0'), w.inst('ccatrn')], 'syl2anc',
               '( %s -> ran %s = ( ran %s u. ran u ) )' % (SB, SU, SW))
    rnsuO = w.s([rnsu, w.s([w.s([swO, sb(rnuO, 'ran u C_ ran O')], 'jca',
                                '( %s -> ( ran %s C_ ran O /\\ ran u C_ ran O ) )' % (SB, SW)),
                            w.s([w.s([], 'unss', '( ( ran %s C_ ran O /\\ ran u C_ ran O ) <-> ( ran %s u. ran u ) C_ ran O )' % (SW, SW))],
                                'a1i', '( %s -> ( ( ran %s C_ ran O /\\ ran u C_ ran O ) <-> ( ran %s u. ran u ) C_ ran O ) )' % (SB, SW, SW))],
                           'mpbid', '( %s -> ( ran %s u. ran u ) C_ ran O )' % (SB, SW))], 'eqsstrd',
                '( %s -> ran %s C_ ran O )' % (SB, SU))
    prdsu = w.s([sww, sb(uu, 'u e. Word NN0'), w.inst('algprodcc')], 'syl2anc',
                '( %s -> %s = ( %s x. %s ) )' % (SB, PRD(SU), PRD(SW), PRD('u')))
    prdmp = w.s([w.s([prdsu, w.s([w.s([sb(mpr, 'm = %s' % PRD('u'))], 'eqcomd', '( %s -> %s = m )' % (SB, PRD('u')))], 'oveq2d',
                                 '( %s -> ( %s x. %s ) = ( %s x. m ) )' % (SB, PRD(SW), PRD('u'), PRD(SW)))], 'eqtrd',
                     '( %s -> %s = ( %s x. m ) )' % (SB, PRD(SU), PRD(SW))),
                 w.s([w.s([w.s([prdn], 'nncnd', '( %s -> %s e. CC )' % (SB, PRD(SW))),
                           w.s([sb(mm, 'm e. NN0')], 'nn0cnd', '( %s -> m e. CC )' % SB)], 'mulcomd',
                          '( %s -> ( %s x. m ) = ( m x. %s ) )' % (SB, PRD(SW), PRD(SW))),
                      w.s([w.s([pseq], 'eqcomd', '( %s -> %s = %s )' % (SB, PRD(SW), PS))], 'oveq2d',
                          '( %s -> ( m x. %s ) = %s )' % (SB, PRD(SW), MPv))], 'eqtrd',
                     '( %s -> ( %s x. m ) = %s )' % (SB, PRD(SW), MPv))], 'eqtrd', '( %s -> %s = %s )' % (SB, PRD(SU), MPv))
    psdv = w.s([sdv, w.s([w.s([pseq], 'oveq1d', '( %s -> ( %s - 1 ) = ( %s - 1 ) )' % (SB, PS, PRD(SW)))], 'eqcomd',
                         '( %s -> ( %s - 1 ) = ( %s - 1 ) )' % (SB, PRD(SW), PS))], 'breqtrd', '( %s -> L || ( %s - 1 ) )' % (SB, PS))
    mpdv = w.s([w.s([w.s([sb(ll, 'L e. NN'), sb(mm, 'm e. NN0'), psn], '3jca',
                         '( %s -> ( L e. NN /\\ m e. NN0 /\\ %s e. NN0 ) )' % (SB, PS)),
                     w.s([sb(mdv, 'L || ( m - 1 )'), psdv], 'jca',
                         '( %s -> ( L || ( m - 1 ) /\\ L || ( %s - 1 ) ) )' % (SB, PS))], 'jca',
                    '( %s -> ( ( L e. NN /\\ m e. NN0 /\\ %s e. NN0 ) /\\ ( L || ( m - 1 ) /\\ L || ( %s - 1 ) ) ) )' % (SB, PS, PS)),
                w.inst('extgol6')], 'syl', '( %s -> L || ( %s - 1 ) )' % (SB, MPv))
    # ( L + 1 ) ^ ( h + 1 ) <_ MPv
    l1n = w.s([sb(ll, 'L e. NN'), w.inst('peano2nn')], 'syl', '( %s -> ( L + 1 ) e. NN )' % SB)
    pwh = w.s([l1n, sb(hh, 'h e. NN0'), w.inst('nnexpcl')], 'syl2anc', '( %s -> ( ( L + 1 ) ^ h ) e. NN )' % SB)
    pwhr = w.s([pwh], 'nnred', '( %s -> ( ( L + 1 ) ^ h ) e. RR )' % SB)
    pwh0 = w.s([w.s([pwh], 'nnnn0d', '( %s -> ( ( L + 1 ) ^ h ) e. NN0 )' % SB)], 'nn0ge0d',
               '( %s -> 0 <_ ( ( L + 1 ) ^ h ) )' % SB)
    l1r = w.s([l1n], 'nnred', '( %s -> ( L + 1 ) e. RR )' % SB)
    l10 = w.s([w.s([l1n], 'nnnn0d', '( %s -> ( L + 1 ) e. NN0 )' % SB)], 'nn0ge0d', '( %s -> 0 <_ ( L + 1 ) )' % SB)
    mr = w.s([sb(mm, 'm e. NN0')], 'nn0red', '( %s -> m e. RR )' % SB)
    psr = w.s([psn], 'nn0red', '( %s -> %s e. RR )' % (SB, PS))
    sgeps = w.s([sge, w.s([pseq], 'eqcomd', '( %s -> %s = %s )' % (SB, PRD(SW), PS))], 'breqtrd',
                '( %s -> ( L + 1 ) <_ %s )' % (SB, PS))
    mul12 = w.s([w.s([w.s([w.s([pwhr, pwh0], 'jca', '( %s -> ( ( ( L + 1 ) ^ h ) e. RR /\\ 0 <_ ( ( L + 1 ) ^ h ) ) )' % SB),
                           mr], 'jca',
                          '( %s -> ( ( ( ( L + 1 ) ^ h ) e. RR /\\ 0 <_ ( ( L + 1 ) ^ h ) ) /\\ m e. RR ) )' % SB),
                      w.s([w.s([l1r, l10], 'jca', '( %s -> ( ( L + 1 ) e. RR /\\ 0 <_ ( L + 1 ) ) )' % SB), psr], 'jca',
                          '( %s -> ( ( ( L + 1 ) e. RR /\\ 0 <_ ( L + 1 ) ) /\\ %s e. RR ) )' % (SB, PS))], 'jca',
                     '( %s -> ( ( ( ( ( L + 1 ) ^ h ) e. RR /\\ 0 <_ ( ( L + 1 ) ^ h ) ) /\\ m e. RR ) /\\ ( ( ( L + 1 ) e. RR /\\ 0 <_ ( L + 1 ) ) /\\ %s e. RR ) ) )' % (SB, PS)),
                 w.inst('lemul12a')], 'syl',
                '( %s -> ( ( ( ( L + 1 ) ^ h ) <_ m /\\ ( L + 1 ) <_ %s ) -> ( ( ( L + 1 ) ^ h ) x. ( L + 1 ) ) <_ %s ) )' % (SB, PS, MPv))
    pwh1 = w.s([mul12, w.s([sb(pwle, '( ( L + 1 ) ^ h ) <_ m'), sgeps], 'jca',
                           '( %s -> ( ( ( L + 1 ) ^ h ) <_ m /\\ ( L + 1 ) <_ %s ) )' % (SB, PS))], 'mpd',
               '( %s -> ( ( ( L + 1 ) ^ h ) x. ( L + 1 ) ) <_ %s )' % (SB, MPv))
    pwexp = w.s([w.s([l1r], 'recnd', '( %s -> ( L + 1 ) e. CC )' % SB), sb(hh, 'h e. NN0')], 'expp1d',
                '( %s -> ( ( L + 1 ) ^ ( h + 1 ) ) = ( ( ( L + 1 ) ^ h ) x. ( L + 1 ) ) )' % SB)
    pwfin = w.s([pwexp, pwh1], 'eqbrtrd', '( %s -> ( ( L + 1 ) ^ ( h + 1 ) ) <_ %s )' % (SB, MPv))
    # MPv <_ N x. X ^ B
    nr = w.s([sb(nn, 'N e. NN0')], 'nn0red', '( %s -> N e. RR )' % SB)
    m0 = w.s([sb(mm, 'm e. NN0')], 'nn0ge0d', '( %s -> 0 <_ m )' % SB)
    ps0 = w.s([psn], 'nn0ge0d', '( %s -> 0 <_ %s )' % (SB, PS))
    xbr = w.s([w.s([sb(xx, 'X e. NN0'), w.s([sb(bb, 'B e. NN')], 'nnnn0d', '( %s -> B e. NN0 )' % SB)], 'nn0expcld',
                   '( %s -> ( X ^ B ) e. NN0 )' % SB)], 'nn0red', '( %s -> ( X ^ B ) e. RR )' % SB)
    psxb = w.s([pseq, l4], 'eqbrtrd',
               '( %s -> %s <_ ( X ^ B ) )' % (SB, PS))
    mulnb = w.s([w.s([w.s([w.s([mr, m0], 'jca', '( %s -> ( m e. RR /\\ 0 <_ m ) )' % SB), nr], 'jca',
                          '( %s -> ( ( m e. RR /\\ 0 <_ m ) /\\ N e. RR ) )' % SB),
                      w.s([w.s([psr, ps0], 'jca', '( %s -> ( %s e. RR /\\ 0 <_ %s ) )' % (SB, PS, PS)), xbr], 'jca',
                          '( %s -> ( ( %s e. RR /\\ 0 <_ %s ) /\\ ( X ^ B ) e. RR ) )' % (SB, PS, PS))], 'jca',
                     '( %s -> ( ( ( m e. RR /\\ 0 <_ m ) /\\ N e. RR ) /\\ ( ( %s e. RR /\\ 0 <_ %s ) /\\ ( X ^ B ) e. RR ) ) )' % (SB, PS, PS)),
                 w.inst('lemul12a')], 'syl',
                '( %s -> ( ( m <_ N /\\ %s <_ ( X ^ B ) ) -> %s <_ ( N x. ( X ^ B ) ) ) )' % (SB, PS, MPv))
    mpxb = w.s([mulnb, w.s([sb(mle, 'm <_ N'), psxb], 'jca', '( %s -> ( m <_ N /\\ %s <_ ( X ^ B ) ) )' % (SB, PS))], 'mpd',
               '( %s -> %s <_ ( N x. ( X ^ B ) ) )' % (SB, MPv))
    # ---- the value at a hit
    EGR = EG('V', MPv, SU, 'EmptyTbl')
    TH1 = '( inl ` <. %s , %s >. )' % (MPv, SU)
    TH2 = '( ( ( 2nd ` %s ) + ( 2nd ` ( ProdL ` %s ) ) ) + 1 )' % (DSP, SW)
    EL2 = '( ( ( ( 2nd ` %s ) + ( 2nd ` %s ) ) + ( 2nd ` ( ProdL ` %s ) ) ) + 1 )' % (EGR, DSP, SW)
    COND = 'N < %s' % MPv
    IFE = 'if ( %s , <. %s , %s >. , <. %s , %s >. )' % (COND, TH1, TH2, F1(EGR), EL2)
    llS = sb(ll, 'L e. NN'); nnS = sb(nn, 'N e. NN0'); mmS = sb(mm, 'm e. NN0'); uuS = sb(uu, 'u e. Word NN0')
    ttS = sb(tt, 't e. Tbl'); ppS = sb(pp, 'P e. NN0'); vvS = sb(vv, 'V e. Word NN0')
    ajs, _fs = lnest(w, SB, [(w.s([llS, nnS], 'jca', '( %s -> ( L e. NN /\\ N e. NN0 ) )' % SB), '( L e. NN /\\ N e. NN0 )'),
                             (mmS, 'm e. NN0'), (uuS, 'u e. Word NN0'), (ttS, 't e. Tbl'),
                             (ppS, 'P e. NN0'), (vvS, 'V e. Word NN0'), (hitne, '%s =/= %s' % (HITV, NONE))])
    vals = w.s([ajs, w.inst('extractgocss')], 'syl', '( %s -> %s = %s )' % (SB, EG(CSV, 'm', 'u', 't'), IFE))
    ift, iff = ifproj(w, SB, EG(CSV, 'm', 'u', 't'), vals, COND, '<. %s , %s >.' % (TH1, TH2), '<. %s , %s >.' % (F1(EGR), EL2))
    # ---------------------------------------- the return branch
    RT = '( %s /\\ %s )' % (SB, COND)
    rt = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (RT, f))
    EGC = EG(CSV, 'm', 'u', 't')
    opx = w.s([w.s([], 'opex', '<. %s , %s >. e. _V' % (MPv, SU))], 'a1i', '( %s -> <. %s , %s >. e. _V )' % (RT, MPv, SU))
    pt = prj(w, RT, EGC, ift, TH1, TH2, 1,
             aex=w.s([w.s([], 'fvex', '%s e. _V' % TH1)], 'a1i', '( %s -> %s e. _V )' % (RT, TH1)),
             bex=w.s([w.s([], 'ovex', '%s e. _V' % TH2)], 'a1i', '( %s -> %s e. _V )' % (RT, TH2)))
    nnone = w.s([w.s([opx, pt], 'jca', '( %s -> ( <. %s , %s >. e. _V /\\ %s = %s ) )' % (RT, MPv, SU, F1(EGC), TH1)),
                 w.inst('algnne')], 'syl', '( %s -> %s =/= %s )' % (RT, F1(EGC), NONE))
    pay = w.s([w.s([pt], 'fveq2d', '( %s -> ( 2nd ` %s ) = ( 2nd ` %s ) )' % (RT, F1(EGC), TH1)),
               w.s([opx, w.inst('alginl2')], 'syl', '( %s -> ( 2nd ` %s ) = <. %s , %s >. )' % (RT, TH1, MPv, SU))], 'eqtrd',
              '( %s -> ( 2nd ` %s ) = <. %s , %s >. )' % (RT, F1(EGC), MPv, SU))
    mpex = w.s([rt(mpn, '%s e. NN0' % MPv)], 'elexd', '( %s -> %s e. _V )' % (RT, MPv))
    suex = w.s([rt(suw, '%s e. Word NN0' % SU)], 'elexd', '( %s -> %s e. _V )' % (RT, SU))
    MMr = MMe(EGC); SSr = SSe(EGC)
    mmeq = w.s([w.s([pay], 'fveq2d', '( %s -> %s = ( 1st ` <. %s , %s >. ) )' % (RT, MMr, MPv, SU)),
                w.s([mpex, suex, w.inst('op1stg')], 'syl2anc', '( %s -> ( 1st ` <. %s , %s >. ) = %s )' % (RT, MPv, SU, MPv))], 'eqtrd',
               '( %s -> %s = %s )' % (RT, MMr, MPv))
    sseq = w.s([w.s([pay], 'fveq2d', '( %s -> %s = ( 2nd ` <. %s , %s >. ) )' % (RT, SSr, MPv, SU)),
                w.s([mpex, suex, w.inst('op2ndg')], 'syl2anc', '( %s -> ( 2nd ` <. %s , %s >. ) = %s )' % (RT, MPv, SU, SU))], 'eqtrd',
               '( %s -> %s = %s )' % (RT, SSr, SU))
    fuss = w.s([rt(fusu, "Fun `' %s" % SU),
                w.s([w.s([sseq], 'cnveqd', "( %s -> `' %s = `' %s )" % (RT, SSr, SU))], 'funeqd',
                    "( %s -> ( Fun `' %s <-> Fun `' %s ) )" % (RT, SSr, SU))], 'mpbird', "( %s -> Fun `' %s )" % (RT, SSr))
    rnss = w.s([w.s([sseq], 'rneqd', '( %s -> ran %s = ran %s )' % (RT, SSr, SU)), rt(rnsuO, 'ran %s C_ ran O' % SU)], 'eqsstrd',
               '( %s -> ran %s C_ ran O )' % (RT, SSr))
    prss = w.s([prdeq(w, RT, SSr, SU, sseq),
                w.s([rt(prdmp, '%s = %s' % (PRD(SU), MPv)),
                     w.s([mmeq], 'eqcomd', '( %s -> %s = %s )' % (RT, MPv, MMr))], 'eqtrd',
                    '( %s -> %s = %s )' % (RT, PRD(SU), MMr))], 'eqtrd', '( %s -> %s = %s )' % (RT, PRD(SSr), MMr))
    mmdv = w.s([rt(mpdv, 'L || ( %s - 1 )' % MPv),
                w.s([w.s([mmeq], 'oveq1d', '( %s -> ( %s - 1 ) = ( %s - 1 ) )' % (RT, MMr, MPv))], 'eqcomd',
                    '( %s -> ( %s - 1 ) = ( %s - 1 ) )' % (RT, MPv, MMr))], 'breqtrd', '( %s -> L || ( %s - 1 ) )' % (RT, MMr))
    mmlt = w.s([w.s([], 'simpr', '( %s -> %s )' % (RT, COND)),
                w.s([mmeq], 'eqcomd', '( %s -> %s = %s )' % (RT, MPv, MMr))], 'breqtrd', '( %s -> N < %s )' % (RT, MMr))
    mmle = w.s([mmeq, rt(mpxb, '%s <_ ( N x. ( X ^ B ) )' % MPv)], 'eqbrtrd', '( %s -> %s <_ ( N x. ( X ^ B ) ) )' % (RT, MMr))
    gt = w.s([nnone, w.s([fuss, rnss, prss], '3jca',
                         "( %s -> ( Fun `' %s /\\ ran %s C_ ran O /\\ %s = %s ) )" % (RT, SSr, SSr, PRD(SSr), MMr)),
              w.s([mmdv, mmlt, mmle], '3jca',
                  '( %s -> ( L || ( %s - 1 ) /\\ N < %s /\\ %s <_ ( N x. ( X ^ B ) ) ) )' % (RT, MMr, MMr, MMr))], '3jca',
             '( %s -> %s )' % (RT, OUTC(CSV, 'm', 'u', 't')))
    # ---------------------------------------- the reset branch
    RS = '( %s /\\ -. %s )' % (SB, COND)
    rs = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (RS, f))
    pf = prj(w, RS, EGC, iff, F1(EGR), EL2, 1,
             aex=w.s([w.s([], 'fvex', '%s e. _V' % F1(EGR))], 'a1i', '( %s -> %s e. _V )' % (RS, F1(EGR))),
             bex=w.s([w.s([], 'ovex', '%s e. _V' % EL2)], 'a1i', '( %s -> %s e. _V )' % (RS, EL2)))
    rn0e = w.s([w.s([], 'rn0', 'ran (/) = (/)')], 'a1i', '( %s -> ran (/) = (/) )' % RS)
    z0ss = w.s([rn0e, w.s([w.s([], '0ss', '(/) C_ ran O')], 'a1i', '( %s -> (/) C_ ran O )' % RS)], 'eqsstrd',
               '( %s -> ran (/) C_ ran O )' % RS)
    def zdisj(w, ante, other):
        return w.s([w.s([w.s([], 'rn0', 'ran (/) = (/)')], 'a1i', '( %s -> ran (/) = (/) )' % ante)], 'ineq1d',
                   '( %s -> ( ran (/) i^i %s ) = ( (/) i^i %s ) )' % (ante, other, other))
    z1 = w.s([zdisj(w, RS, 'ran V'), w.s([w.s([], '0in', '( (/) i^i ran V ) = (/)')], 'a1i',
                                         '( %s -> ( (/) i^i ran V ) = (/) )' % RS)], 'eqtrd',
             '( %s -> ( ran (/) i^i ran V ) = (/) )' % RS)
    z2 = w.s([zdisj(w, RS, 'ran %s' % SU), w.s([w.s([], '0in', '( (/) i^i ran %s ) = (/)' % SU)], 'a1i',
                                               '( %s -> ( (/) i^i ran %s ) = (/) )' % (RS, SU))], 'eqtrd',
             '( %s -> ( ran (/) i^i ran %s ) = (/) )' % (RS, SU))
    swv = w.s([w.s([swce, sb(dcev, '( ran %s i^i ran V ) = (/)' % CSE)], 'jca',
                   '( %s -> ( ran %s C_ ran %s /\\ ( ran %s i^i ran V ) = (/) ) )' % (SB, SW, CSE, CSE)), w.inst('ssdisj')], 'syl',
              '( %s -> ( ran %s i^i ran V ) = (/) )' % (SB, SW))
    dsuv0 = w.s([w.s([swv, sb(duv, '( ran u i^i ran V ) = (/)')], 'jca',
                     '( %s -> ( ( ran %s i^i ran V ) = (/) /\\ ( ran u i^i ran V ) = (/) ) )' % (SB, SW)),
                 w.s([w.s([], 'undisj1',
                           '( ( ( ran %s i^i ran V ) = (/) /\\ ( ran u i^i ran V ) = (/) ) <-> ( ( ran %s u. ran u ) i^i ran V ) = (/) )' % (SW, SW))],
                     'a1i',
                     '( %s -> ( ( ( ran %s i^i ran V ) = (/) /\\ ( ran u i^i ran V ) = (/) ) <-> ( ( ran %s u. ran u ) i^i ran V ) = (/) ) )' % (SB, SW, SW))],
                'mpbid', '( %s -> ( ( ran %s u. ran u ) i^i ran V ) = (/) )' % (SB, SW))
    dsuv = w.s([w.s([rnsu], 'ineq1d', '( %s -> ( ran %s i^i ran V ) = ( ( ran %s u. ran u ) i^i ran V ) )' % (SB, SU, SW)),
                dsuv0], 'eqtrd', '( %s -> ( ran %s i^i ran V ) = (/) )' % (SB, SU))
    mpr2 = w.s([rs(mr, 'm e. RR'), rs(psr, '%s e. RR' % PS)], 'remulcld', '( %s -> %s e. RR )' % (RS, MPv))
    mpleN = w.s([w.s([mpr2, rs(nr, 'N e. RR')], 'lenltd', '( %s -> ( %s <_ N <-> -. N < %s ) )' % (RS, MPv, MPv)),
                 w.s([], 'simpr', '( %s -> -. %s )' % (RS, COND))], 'mpbird', '( %s -> %s <_ N )' % (RS, MPv))
    w0 = w.s([w.s([], 'wrd0', '(/) e. Word NN0')], 'a1i', '( %s -> (/) e. Word NN0 )' % RS)
    etc = w.s([w.s([], 'emptytblcl', 'EmptyTbl e. Tbl')], 'a1i', '( %s -> EmptyTbl e. Tbl )' % RS)
    tsz = w.s([w.s([rs(sb(ll, 'L e. NN'), 'L e. NN'), w0], 'jca', '( %s -> ( L e. NN /\\ (/) e. Word NN0 ) )' % RS),
               w.inst('tblsnd0')], 'syl', '( %s -> %s )' % (RS, TS('L', 'EmptyTbl', '(/)')))
    tcz = w.s([rs(sb(ll, 'L e. NN'), 'L e. NN'), w.inst('tblcmp0')], 'syl', '( %s -> %s )' % (RS, TC('L', 'EmptyTbl', '(/)')))
    b0 = w.s([w.s([w.s([], 'hash0', '( # ` (/) ) = 0')], 'a1i', '( %s -> ( # ` (/) ) = 0 )' % RS),
              w.s([rs(sb(bb, 'B e. NN'), 'B e. NN')], 'nngt0d', '( %s -> 0 < B )' % RS)], 'eqbrtrd',
             '( %s -> ( # ` (/) ) < B )' % RS)
    # the supply inequality after the reset
    cbf = w.s([w.s([w.s([rs(sb(lgbr, '( ( %s + 1 ) x. B ) e. RR' % LG), '( ( %s + 1 ) x. B ) e. RR' % LG),
                         rs(sb(lvr, '( # ` V ) e. RR'), '( # ` V ) e. RR'),
                         rs(sb(hbr, '( h x. B ) e. RR'), '( h x. B ) e. RR')], '3jca',
                        '( %s -> ( ( ( %s + 1 ) x. B ) e. RR /\\ ( # ` V ) e. RR /\\ ( h x. B ) e. RR ) )' % (RS, LG)),
                    w.s([rs(sb(ler, '( # ` e ) e. RR'), '( # ` e ) e. RR'), rs(sb(br, 'B e. RR'), 'B e. RR')], 'jca',
                        '( %s -> ( ( # ` e ) e. RR /\\ B e. RR ) )' % RS),
                    w.s([rs(sb(supv, '( ( %s + 1 ) x. B ) <_ ( ( ( ( # ` V ) + 1 ) + ( h x. B ) ) + ( # ` e ) )' % LG),
                            '( ( %s + 1 ) x. B ) <_ ( ( ( ( # ` V ) + 1 ) + ( h x. B ) ) + ( # ` e ) )' % LG),
                         rs(lep1S, '( ( # ` e ) + 1 ) <_ B')], 'jca',
                        '( %s -> ( ( ( %s + 1 ) x. B ) <_ ( ( ( ( # ` V ) + 1 ) + ( h x. B ) ) + ( # ` e ) ) /\\ ( ( # ` e ) + 1 ) <_ B ) )' % (RS, LG))],
                   '3jca',
                   '( %s -> ( ( ( ( %s + 1 ) x. B ) e. RR /\\ ( # ` V ) e. RR /\\ ( h x. B ) e. RR ) /\\ ( ( # ` e ) e. RR /\\ B e. RR ) /\\ ( ( ( %s + 1 ) x. B ) <_ ( ( ( ( # ` V ) + 1 ) + ( h x. B ) ) + ( # ` e ) ) /\\ ( ( # ` e ) + 1 ) <_ B ) ) )' % (RS, LG, LG)),
               w.inst('extgocbf')], 'syl',
              '( %s -> ( ( %s + 1 ) x. B ) <_ ( ( ( # ` V ) + ( ( h x. B ) + B ) ) + 0 ) )' % (RS, LG))
    hdist = w.s([w.s([rs(sb(w.s([hh], 'nn0cnd', '( %s -> h e. CC )' % U), 'h e. CC'), 'h e. CC'),
                      rs(sb(w.s([bb], 'nncnd', '( %s -> B e. CC )' % U), 'B e. CC'), 'B e. CC')], 'adddirp1d',
                     '( %s -> ( ( h + 1 ) x. B ) = ( ( h x. B ) + B ) )' % RS)], 'eqcomd',
                '( %s -> ( ( h x. B ) + B ) = ( ( h + 1 ) x. B ) )' % RS)
    supr = w.s([cbf, w.s([w.s([hdist], 'oveq2d',
                              '( %s -> ( ( # ` V ) + ( ( h x. B ) + B ) ) = ( ( # ` V ) + ( ( h + 1 ) x. B ) ) )' % RS)], 'oveq1d',
                         '( %s -> ( ( ( # ` V ) + ( ( h x. B ) + B ) ) + 0 ) = ( ( ( # ` V ) + ( ( h + 1 ) x. B ) ) + 0 ) )' % RS)],
               'breqtrd', '( %s -> ( ( %s + 1 ) x. B ) <_ ( ( ( # ` V ) + ( ( h + 1 ) x. B ) ) + 0 ) )' % (RS, LG))
    supr2 = w.s([supr, w.s([w.s([w.s([w.s([], 'hash0', '( # ` (/) ) = 0')], 'a1i', '( %s -> ( # ` (/) ) = 0 )' % RS)], 'eqcomd',
                                '( %s -> 0 = ( # ` (/) ) )' % RS)], 'oveq2d',
                           '( %s -> ( ( ( # ` V ) + ( ( h + 1 ) x. B ) ) + 0 ) = ( ( ( # ` V ) + ( ( h + 1 ) x. B ) ) + ( # ` (/) ) ) )' % RS)],
                'breqtrd', '( %s -> %s )' % (RS, SUPX('V', '(/)', '( h + 1 )')))
    invr = w.s([w.s([w.s([rs(fusu, "Fun `' %s" % SU), rs(rnsuO, 'ran %s C_ ran O' % SU),
                          rs(dsuv, '( ran %s i^i ran V ) = (/)' % SU)], '3jca', '( %s -> %s )' % (RS, IU('V', SU))),
                     w.s([w.s([w.s([w.s([], 'algndp0', "Fun `' (/)")], 'a1i', "( %s -> Fun `' (/) )" % RS), z0ss], 'jca',
                              "( %s -> ( Fun `' (/) /\\ ran (/) C_ ran O ) )" % RS),
                          w.s([z1, z2], 'jca',
                              '( %s -> ( ( ran (/) i^i ran V ) = (/) /\\ ( ran (/) i^i ran %s ) = (/) ) )' % (RS, SU))], 'jca',
                         '( %s -> %s )' % (RS, IE('V', SU, '(/)')))], 'jca',
                    '( %s -> ( %s /\\ %s ) )' % (RS, IU('V', SU), IE('V', SU, '(/)'))),
                w.s([w.s([w.s([rs(prdmp, '%s = %s' % (PRD(SU), MPv))], 'eqcomd', '( %s -> %s = %s )' % (RS, MPv, PRD(SU))),
                          rs(mpdv, 'L || ( %s - 1 )' % MPv), mpleN], '3jca', '( %s -> %s )' % (RS, IM(MPv, SU))),
                     w.s([tsz, tcz, b0], '3jca', '( %s -> %s )' % (RS, IT('EmptyTbl', '(/)')))], 'jca',
                    '( %s -> ( %s /\\ %s ) )' % (RS, IM(MPv, SU), IT('EmptyTbl', '(/)'))),
                w.s([rs(pwfin, '( ( L + 1 ) ^ ( h + 1 ) ) <_ %s' % MPv), supr2], 'jca',
                    '( %s -> %s )' % (RS, IHc('V', MPv, '(/)', '( h + 1 )')))], '3jca',
               '( %s -> %s )' % (RS, INV('V', MPv, SU, '(/)', 'EmptyTbl', '( h + 1 )')))
    h1n = w.s([rs(sb(hh, 'h e. NN0'), 'h e. NN0'), w.inst('peano2nn0')], 'syl', '( %s -> ( h + 1 ) e. NN0 )' % RS)
    ihr, _ = instn(w, RS, rs(sb(ih, ctx.ihf), ctx.ihf),
                   [(r[0], 'NN0'), (r[1], 'Word NN0'), (r[2], 'Word NN0'), (r[3], 'Tbl'), (r[4], 'NN0')],
                   ihb, [MPv, SU, '(/)', 'EmptyTbl', '( h + 1 )'],
                   [rs(mpn, '%s e. NN0' % MPv), rs(suw, '%s e. Word NN0' % SU), w0, etc, h1n])
    gotr = w.s([ihr, w.s([rs(sb(wcv, WC('V')), WC('V')), invr], 'jca',
                         '( %s -> ( %s /\\ %s ) )' % (RS, WC('V'), INV('V', MPv, SU, '(/)', 'EmptyTbl', '( h + 1 )')))], 'mpd',
               '( %s -> %s )' % (RS, OUTC('V', MPv, SU, 'EmptyTbl')))
    trr = outtrans(w, RS, (CSV, 'm', 'u', 't'), ('V', MPv, SU, 'EmptyTbl'), pf)
    gr = w.s([gotr, trr], 'mpbird', '( %s -> %s )' % (RS, OUTC(CSV, 'm', 'u', 't')))
    gs = w.s([gt, gr], 'pm2.61dan', '( %s -> %s )' % (SB, OUTC(CSV, 'm', 'u', 't')))
    fin = w.s([gn, gs], 'pm2.61dan', '( %s -> %s )' % (U, OUTC(CSV, 'm', 'u', 't')))
    return w.s([fin], 'ex', '( %s -> %s )' % (A, goal))

def _i(w):
    pass

qwrd(run, 'extgospec', ESO, QU, BODY, _b, _s, only=only, svar='y', prods=(SSe(EG('y', 'm', 'u', 't')),),
     desc='The round argument for the extraction loop (Lean: extractGo_spec).')

# ================================================================= extspec
if not only or 'extspec' in only:
    w = W('extspec', 'Step 4 extracts a product congruent to one above n (Lean: extract_spec).')
    SW_ = lambda x: subst(x, 'O', 'W')
    ESOW = SW_(ESO); VEBKW = SW_(VEBK)
    EX = '( ( L Extract N ) ` W )'
    EGW = EG('W', '1', '(/)', 'EmptyTbl')
    A = ('( ( ( L e. NN /\\ 2 <_ L ) /\\ ( N e. NN0 /\\ 1 <_ N ) /\\ ( X e. NN0 /\\ B e. NN /\\ W e. Word NN0 ) ) /\\ '
         "( Fun `' W /\\ A. p e. ran W ( 2 <_ p /\\ p <_ X ) ) /\\ "
         '( %s /\\ ( ( %s + 1 ) x. B ) <_ ( # ` W ) ) )' % (VEBKW, LG))
    ll = w.s([w.s([], 'simp1', '( %s -> ( ( L e. NN /\\ 2 <_ L ) /\\ ( N e. NN0 /\\ 1 <_ N ) /\\ ( X e. NN0 /\\ B e. NN /\\ W e. Word NN0 ) ) )' % A)],
             'simp1d', '( %s -> ( L e. NN /\\ 2 <_ L ) )' % A)
    nn1 = w.s([w.s([], 'simp1', '( %s -> ( ( L e. NN /\\ 2 <_ L ) /\\ ( N e. NN0 /\\ 1 <_ N ) /\\ ( X e. NN0 /\\ B e. NN /\\ W e. Word NN0 ) ) )' % A)],
              'simp2d', '( %s -> ( N e. NN0 /\\ 1 <_ N ) )' % A)
    xbw = w.s([w.s([], 'simp1', '( %s -> ( ( L e. NN /\\ 2 <_ L ) /\\ ( N e. NN0 /\\ 1 <_ N ) /\\ ( X e. NN0 /\\ B e. NN /\\ W e. Word NN0 ) ) )' % A)],
              'simp3d', '( %s -> ( X e. NN0 /\\ B e. NN /\\ W e. Word NN0 ) )' % A)
    lln = w.s([ll], 'simpld', '( %s -> L e. NN )' % A)
    ll2 = w.s([ll], 'simprd', '( %s -> 2 <_ L )' % A)
    nn = w.s([nn1], 'simpld', '( %s -> N e. NN0 )' % A)
    n1 = w.s([nn1], 'simprd', '( %s -> 1 <_ N )' % A)
    xx = w.s([xbw], 'simp1d', '( %s -> X e. NN0 )' % A)
    bb = w.s([xbw], 'simp2d', '( %s -> B e. NN )' % A)
    ww = w.s([xbw], 'simp3d', '( %s -> W e. Word NN0 )' % A)
    fuw = w.s([w.s([], 'simp2', "( %s -> ( Fun `' W /\\ A. p e. ran W ( 2 <_ p /\\ p <_ X ) ) )" % A)], 'simpld',
              "( %s -> Fun `' W )" % A)
    wpr = w.s([w.s([], 'simp2', "( %s -> ( Fun `' W /\\ A. p e. ran W ( 2 <_ p /\\ p <_ X ) ) )" % A)], 'simprd',
              '( %s -> A. p e. ran W ( 2 <_ p /\\ p <_ X ) )' % A)
    vb = w.s([w.s([], 'simp3', '( %s -> ( %s /\\ ( ( %s + 1 ) x. B ) <_ ( # ` W ) ) )' % (A, VEBKW, LG))], 'simpld',
             '( %s -> %s )' % (A, VEBKW))
    sup = w.s([w.s([], 'simp3', '( %s -> ( %s /\\ ( ( %s + 1 ) x. B ) <_ ( # ` W ) ) )' % (A, VEBKW, LG))], 'simprd',
              '( %s -> ( ( %s + 1 ) x. B ) <_ ( # ` W ) )' % (A, LG))
    eso = w.s([ll, w.s([nn, xx, bb], '3jca', '( %s -> ( N e. NN0 /\\ X e. NN0 /\\ B e. NN ) )' % A),
               w.s([ww, wpr, vb], '3jca', '( %s -> ( W e. Word NN0 /\\ A. p e. ran W ( 2 <_ p /\\ p <_ X ) /\\ %s ) )' % (A, VEBKW))],
              '3jca', '( %s -> %s )' % (A, ESOW))
    # the invariant at the start
    wc = w.s([fuw, w.s([w.s([], 'ssid', 'ran W C_ ran W')], 'a1i', '( %s -> ran W C_ ran W )' % A)], 'jca',
             '( %s -> %s )' % (A, SW_(WC('W'))))
    z0ss = w.s([w.s([w.s([], 'rn0', 'ran (/) = (/)')], 'a1i', '( %s -> ran (/) = (/) )' % A),
                w.s([w.s([], '0ss', '(/) C_ ran W')], 'a1i', '( %s -> (/) C_ ran W )' % A)], 'eqsstrd',
               '( %s -> ran (/) C_ ran W )' % A)
    def zd(other):
        return w.s([w.s([w.s([w.s([], 'rn0', 'ran (/) = (/)')], 'a1i', '( %s -> ran (/) = (/) )' % A)], 'ineq1d',
                        '( %s -> ( ran (/) i^i %s ) = ( (/) i^i %s ) )' % (A, other, other)),
                    w.s([w.s([], '0in', '( (/) i^i %s ) = (/)' % other)], 'a1i', '( %s -> ( (/) i^i %s ) = (/) )' % (A, other))],
                   'eqtrd', '( %s -> ( ran (/) i^i %s ) = (/) )' % (A, other))
    fu0 = w.s([w.s([], 'algndp0', "Fun `' (/)")], 'a1i', "( %s -> Fun `' (/) )" % A)
    iu = w.s([fu0, z0ss, zd('ran W')], '3jca', '( %s -> %s )' % (A, SW_(IU('W', '(/)'))))
    ie = w.s([w.s([fu0, z0ss], 'jca', "( %s -> ( Fun `' (/) /\\ ran (/) C_ ran W ) )" % A),
              w.s([zd('ran W'), zd('ran (/)')], 'jca',
                  '( %s -> ( ( ran (/) i^i ran W ) = (/) /\\ ( ran (/) i^i ran (/) ) = (/) ) )' % A)], 'jca',
             '( %s -> %s )' % (A, SW_(IE('W', '(/)', '(/)'))))
    p0 = w.s([w.s([w.s([], 'algprod0', '%s = 1' % PRD('(/)'))], 'a1i', '( %s -> %s = 1 )' % (A, PRD('(/)')))], 'eqcomd',
             '( %s -> 1 = %s )' % (A, PRD('(/)')))
    d0 = w.s([w.s([w.s([lln], 'nnzd', '( %s -> L e. ZZ )' % A), w.inst('dvds0')], 'syl', '( %s -> L || 0 )' % A),
              w.s([w.s([w.s([], '1m1e0', '( 1 - 1 ) = 0')], 'a1i', '( %s -> ( 1 - 1 ) = 0 )' % A)], 'eqcomd',
                  '( %s -> 0 = ( 1 - 1 ) )' % A)], 'breqtrd', '( %s -> L || ( 1 - 1 ) )' % A)
    im = w.s([p0, d0, n1], '3jca', '( %s -> %s )' % (A, IM('1', '(/)')))
    w0 = w.s([w.s([], 'wrd0', '(/) e. Word NN0')], 'a1i', '( %s -> (/) e. Word NN0 )' % A)
    tsz = w.s([w.s([lln, w0], 'jca', '( %s -> ( L e. NN /\\ (/) e. Word NN0 ) )' % A), w.inst('tblsnd0')], 'syl',
              '( %s -> %s )' % (A, TS('L', 'EmptyTbl', '(/)')))
    tcz = w.s([lln, w.inst('tblcmp0')], 'syl', '( %s -> %s )' % (A, TC('L', 'EmptyTbl', '(/)')))
    b0 = w.s([w.s([w.s([], 'hash0', '( # ` (/) ) = 0')], 'a1i', '( %s -> ( # ` (/) ) = 0 )' % A),
              w.s([bb], 'nngt0d', '( %s -> 0 < B )' % A)], 'eqbrtrd', '( %s -> ( # ` (/) ) < B )' % A)
    it = w.s([tsz, tcz, b0], '3jca', '( %s -> %s )' % (A, IT('EmptyTbl', '(/)')))
    l1c = w.s([w.s([w.s([lln, w.inst('peano2nn')], 'syl', '( %s -> ( L + 1 ) e. NN )' % A)], 'nncnd',
                   '( %s -> ( L + 1 ) e. CC )' % A), w.inst('exp0')], 'syl', '( %s -> ( ( L + 1 ) ^ 0 ) = 1 )' % A)
    pw0 = w.s([l1c, w.s([w.s([w.s([], '1re', '1 e. RR'), w.inst('leid')], 'ax-mp', '1 <_ 1')], 'a1i',
                        '( %s -> 1 <_ 1 )' % A)], 'eqbrtrd', '( %s -> ( ( L + 1 ) ^ 0 ) <_ 1 )' % A)
    lwr = w.s([w.s([ww, w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % A)], 'nn0red', '( %s -> ( # ` W ) e. RR )' % A)
    br = w.s([bb], 'nnred', '( %s -> B e. RR )' % A)
    l1n0 = w.s([w.s([lln, w.inst('peano2nn')], 'syl', '( %s -> ( L + 1 ) e. NN )' % A)], 'nnnn0d',
               '( %s -> ( L + 1 ) e. NN0 )' % A)
    lgn = w.s([l1n0, nn, w.inst('nlogcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (A, LG))
    lgbr = w.s([w.s([w.s([lgn], 'nn0red', '( %s -> %s e. RR )' % (A, LG)), w.inst('peano2re')], 'syl',
                    '( %s -> ( %s + 1 ) e. RR )' % (A, LG)), br], 'remulcld', '( %s -> ( ( %s + 1 ) x. B ) e. RR )' % (A, LG))
    zb = w.s([w.s([br], 'recnd', '( %s -> B e. CC )' % A)], 'mul02d', '( %s -> ( 0 x. B ) = 0 )' % A)
    rw1 = w.s([w.s([zb], 'oveq2d', '( %s -> ( ( # ` W ) + ( 0 x. B ) ) = ( ( # ` W ) + 0 ) )' % A),
               w.s([w.s([lwr], 'recnd', '( %s -> ( # ` W ) e. CC )' % A)], 'addridd', '( %s -> ( ( # ` W ) + 0 ) = ( # ` W ) )' % A)],
              'eqtrd', '( %s -> ( ( # ` W ) + ( 0 x. B ) ) = ( # ` W ) )' % A)
    rw2 = w.s([w.s([rw1], 'oveq1d',
                   '( %s -> ( ( ( # ` W ) + ( 0 x. B ) ) + ( # ` (/) ) ) = ( ( # ` W ) + ( # ` (/) ) ) )' % A),
               w.s([w.s([w.s([w.s([], 'hash0', '( # ` (/) ) = 0')], 'a1i', '( %s -> ( # ` (/) ) = 0 )' % A)], 'oveq2d',
                        '( %s -> ( ( # ` W ) + ( # ` (/) ) ) = ( ( # ` W ) + 0 ) )' % A),
                    w.s([w.s([lwr], 'recnd', '( %s -> ( # ` W ) e. CC )' % A)], 'addridd',
                        '( %s -> ( ( # ` W ) + 0 ) = ( # ` W ) )' % A)], 'eqtrd',
                   '( %s -> ( ( # ` W ) + ( # ` (/) ) ) = ( # ` W ) )' % A)], 'eqtrd',
              '( %s -> ( ( ( # ` W ) + ( 0 x. B ) ) + ( # ` (/) ) ) = ( # ` W ) )' % A)
    supi = w.s([sup, w.s([rw2], 'eqcomd', '( %s -> ( # ` W ) = ( ( ( # ` W ) + ( 0 x. B ) ) + ( # ` (/) ) ) )' % A)], 'breqtrd',
               '( %s -> %s )' % (A, SUPX('W', '(/)', '0')))
    ihc = w.s([pw0, supi], 'jca', '( %s -> %s )' % (A, IHc('W', '1', '(/)', '0')))
    invs = w.s([w.s([iu, ie], 'jca', '( %s -> ( %s /\\ %s ) )' % (A, SW_(IU('W', '(/)')), SW_(IE('W', '(/)', '(/)')))),
                w.s([im, it], 'jca', '( %s -> ( %s /\\ %s ) )' % (A, IM('1', '(/)'), IT('EmptyTbl', '(/)'))), ihc], '3jca',
               '( %s -> %s )' % (A, SW_(INV('W', '1', '(/)', '(/)', 'EmptyTbl', '0'))))
    # extgospec at ( O := W , y := W )
    PHW = subst(subst(BODY, 'y', 'W'), 'O', 'W')
    allyf = SW_(quantify(QU, ['m', 'u', 'e', 't', 'h'], subst(BODY, 'y', 'W')))
    ally0 = w.s([ww, w.inst('extgospec')], 'syl', '( %s -> ( %s -> %s ) )' % (A, ESOW, allyf))
    ally = w.s([ally0, eso], 'mpd', '( %s -> %s )' % (A, allyf))
    styv = ally
    stm, _ = instn(w, A, styv, QU, subst(SW_(BODY), 'y', 'W'), ['1', '(/)', '(/)', 'EmptyTbl', '0'],
                   [w.s([w.s([], '1nn0', '1 e. NN0')], 'a1i', '( %s -> 1 e. NN0 )' % A), w0, w0,
                    w.s([w.s([], 'emptytblcl', 'EmptyTbl e. Tbl')], 'a1i', '( %s -> EmptyTbl e. Tbl )' % A),
                    w.s([w.s([], '0nn0', '0 e. NN0')], 'a1i', '( %s -> 0 e. NN0 )' % A)])
    got = w.s([stm, w.s([wc, invs], 'jca',
                        '( %s -> ( %s /\\ %s ) )' % (A, SW_(WC('W')), SW_(INV('W', '1', '(/)', '(/)', 'EmptyTbl', '0'))))], 'mpd',
              '( %s -> %s )' % (A, SW_(OUTC('W', '1', '(/)', 'EmptyTbl'))))
    val = w.s([w.s([w.s([lln, nn], 'jca', '( %s -> ( L e. NN /\\ N e. NN0 ) )' % A), ww], 'jca',
                   '( %s -> ( ( L e. NN /\\ N e. NN0 ) /\\ W e. Word NN0 ) )' % A), w.inst('extractval')], 'syl',
              '( %s -> %s = %s )' % (A, EX, EGW))
    p1 = w.s([val], 'fveq2d', '( %s -> %s = %s )' % (A, F1(EX), F1(EGW)))
    OLD = F1(EX); NEW = F1(EGW)
    E = '%s = %s' % (OLD, NEW)
    idst = w.s([], 'id', '( %s -> %s )' % (E, E))
    oSS = '( 2nd ` ( 2nd ` %s ) )' % OLD; nSS = '( 2nd ` ( 2nd ` %s ) )' % NEW
    s1 = w.s([idst], 'fveq2d', '( %s -> ( 2nd ` %s ) = ( 2nd ` %s ) )' % (E, OLD, NEW))
    s2 = w.s([s1], 'fveq2d', '( %s -> %s = %s )' % (E, oSS, nSS))
    OUTX = ("( %s =/= %s /\\ ( Fun `' %s /\\ ran %s C_ ran W /\\ %s = %s ) /\\ "
            "( L || ( %s - 1 ) /\\ N < %s /\\ %s <_ ( N x. ( X ^ B ) ) ) )"
            % (OLD, NONE, oSS, oSS, PRD(oSS), '( 1st ` ( 2nd ` %s ) )' % OLD,
               '( 1st ` ( 2nd ` %s ) )' % OLD, '( 1st ` ( 2nd ` %s ) )' % OLD, '( 1st ` ( 2nd ` %s ) )' % OLD))
    rules = {OLD: (NEW, idst), PRD(oSS): (PRD(nSS), prdeq(w, E, oSS, nSS, s2))}
    st, ne = w.wcongr(OUTX, {}, E, {}, rules=rules)
    assert ne == SW_(OUTC('W', '1', '(/)', 'EmptyTbl')), '\n%s\n%s' % (ne, SW_(OUTC('W', '1', '(/)', 'EmptyTbl')))
    tr = w.s([p1, st], 'syl', '( %s -> ( %s <-> %s ) )' % (A, OUTX, ne))
    w.qed([got, tr], 'mpbird', '( %s -> %s )' % (A, OUTX))
    run(w)
