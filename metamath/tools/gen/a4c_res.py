"""Sortie A4c, batch 12: membership and duplicate-freeness of the reservoir
loop (Lean: AlgScan.resGo_mem, resGo_nodup, reservoir_specW)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from a4clib import *
import lin

only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

RG = lambda q, f: '( ( ( Z ResGo Y ) ` %s ) ` %s )' % (q, f)
R1 = lambda q, f: '( 1st ` %s )' % RG(q, f)
IP = lambda q: '( IsPrimeTD ` %s )' % q
SM = lambda q: '( Y SmoothTD ( %s - 1 ) )' % q
KEEP = lambda q: 'if ( Z < %s , if ( ( 1st ` %s ) = 1o , ( 1st ` %s ) , (/) ) , (/) )' % (q, IP(q), SM(q))
SMTH = lambda x: 'A. p e. Prime ( p || ( %s - 1 ) -> p <_ Y )' % x
RHSB = lambda x: '( Z < %s /\\ %s e. Prime /\\ %s )' % (x, x, SMTH(x))

# ------------------------------------------------------------------ resgokeep
if not only or 'resgokeep' in only:
    w = W('resgokeep', 'The reservoir loop keeps exactly the smooth primes above the floor.')
    A = '( ( Z e. NN0 /\\ Y e. NN ) /\\ Q e. NN )'
    zz = w.s([w.s([], 'simpl', '( %s -> ( Z e. NN0 /\\ Y e. NN ) )' % A)], 'simpld', '( %s -> Z e. NN0 )' % A)
    yy = w.s([w.s([], 'simpl', '( %s -> ( Z e. NN0 /\\ Y e. NN ) )' % A)], 'simprd', '( %s -> Y e. NN )' % A)
    qq = w.s([], 'simpr', '( %s -> Q e. NN )' % A)
    qn0 = w.s([qq], 'nnnn0d', '( %s -> Q e. NN0 )' % A)
    INNER = 'if ( ( 1st ` %s ) = 1o , ( 1st ` %s ) , (/) )' % (IP('Q'), SM('Q'))
    # case Z < Q
    C = '( %s /\\ Z < Q )' % A
    c = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (C, f))
    kc = w.s([w.s([], 'simpr', '( %s -> Z < Q )' % C)], 'iftrued', '( %s -> %s = %s )' % (C, KEEP('Q'), INNER))
    #   subcase prime
    D = '( %s /\\ ( 1st ` %s ) = 1o )' % (C, IP('Q'))
    d = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (D, f))
    kd = w.s([d(kc, '%s = %s' % (KEEP('Q'), INNER)),
              w.s([w.s([], 'simpr', '( %s -> ( 1st ` %s ) = 1o )' % (D, IP('Q')))], 'iftrued',
                  '( %s -> %s = ( 1st ` %s ) )' % (D, INNER, SM('Q')))], 'eqtrd',
             '( %s -> %s = ( 1st ` %s ) )' % (D, KEEP('Q'), SM('Q')))
    qpr = w.s([w.s([d(c(qn0, 'Q e. NN0'), 'Q e. NN0'), w.inst('isprimetdspec')], 'syl',
                   '( %s -> ( ( 1st ` %s ) = 1o <-> Q e. Prime ) )' % (D, IP('Q'))),
               w.s([], 'simpr', '( %s -> ( 1st ` %s ) = 1o )' % (D, IP('Q')))], 'mpbid',
              '( %s -> Q e. Prime )' % D)
    q2 = w.s([qpr, w.inst('prmuz2')], 'syl', '( %s -> Q e. ( ZZ>= ` 2 ) )' % D)
    qge2 = w.s([q2, w.inst('eluzle')], 'syl', '( %s -> 2 <_ Q )' % D)
    qr = w.s([d(c(qq, 'Q e. NN'), 'Q e. NN')], 'nnred', '( %s -> Q e. RR )' % D)
    qm1 = w.s([d(c(qq, 'Q e. NN'), 'Q e. NN'), w.inst('nnm1nn0')], 'syl', '( %s -> ( Q - 1 ) e. NN0 )' % D)
    one = lin.linarith(w, D, [qge2], '1 <_ ( Q - 1 )', leaves={'Q': qr})
    sms = w.s([w.s([w.s([d(c(yy, 'Y e. NN'), 'Y e. NN'), qm1], 'jca', '( %s -> ( Y e. NN /\\ ( Q - 1 ) e. NN0 ) )' % D),
                    one], 'jca', '( %s -> ( ( Y e. NN /\\ ( Q - 1 ) e. NN0 ) /\\ 1 <_ ( Q - 1 ) ) )' % D),
               w.inst('smoothtdspec')], 'syl', '( %s -> ( ( 1st ` %s ) = 1o <-> %s ) )' % (D, SM('Q'), SMTH('Q')))
    lhsd = w.s([w.s([kd], 'eqeq1d', '( %s -> ( %s = 1o <-> ( 1st ` %s ) = 1o ) )' % (D, KEEP('Q'), SM('Q'))), sms], 'bitrd',
               '( %s -> ( %s = 1o <-> %s ) )' % (D, KEEP('Q'), SMTH('Q')))
    bt = w.s([w.s([d(w.s([], 'simpr', '( %s -> Z < Q )' % C), 'Z < Q'), qpr], 'jca',
                  '( %s -> ( Z < Q /\\ Q e. Prime ) )' % D)], 'biantrurd',
             '( %s -> ( %s <-> ( ( Z < Q /\\ Q e. Prime ) /\\ %s ) ) )' % (D, SMTH('Q'), SMTH('Q')))
    d3 = w.s([w.s([], 'df-3an', '( %s <-> ( ( Z < Q /\\ Q e. Prime ) /\\ %s ) )' % (RHSB('Q'), SMTH('Q')))], 'a1i',
             '( %s -> ( %s <-> ( ( Z < Q /\\ Q e. Prime ) /\\ %s ) ) )' % (D, RHSB('Q'), SMTH('Q')))
    cd = w.s([lhsd, w.s([bt, w.s([d3], 'bicomd', '( %s -> ( ( ( Z < Q /\\ Q e. Prime ) /\\ %s ) <-> %s ) )' % (D, SMTH('Q'), RHSB('Q')))],
                        'bitrd', '( %s -> ( %s <-> %s ) )' % (D, SMTH('Q'), RHSB('Q')))], 'bitrd',
             '( %s -> ( %s = 1o <-> %s ) )' % (D, KEEP('Q'), RHSB('Q')))
    #   subcase not prime
    E = '( %s /\\ -. ( 1st ` %s ) = 1o )' % (C, IP('Q'))
    e = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (E, f))
    ke = w.s([e(kc, '%s = %s' % (KEEP('Q'), INNER)),
              w.s([w.s([], 'simpr', '( %s -> -. ( 1st ` %s ) = 1o )' % (E, IP('Q')))], 'iffalsed',
                  '( %s -> %s = (/) )' % (E, INNER))], 'eqtrd', '( %s -> %s = (/) )' % (E, KEEP('Q')))
    zn1 = zne1o(w, E)
    lhse = w.s([w.s([ke], 'eqeq1d', '( %s -> ( %s = 1o <-> (/) = 1o ) )' % (E, KEEP('Q'))), zn1], 'mtbird',
               '( %s -> -. %s = 1o )' % (E, KEEP('Q')))
    npr = w.s([w.s([e(c(qn0, 'Q e. NN0'), 'Q e. NN0'), w.inst('isprimetdspec')], 'syl',
                   '( %s -> ( ( 1st ` %s ) = 1o <-> Q e. Prime ) )' % (E, IP('Q'))),
               w.s([], 'simpr', '( %s -> -. ( 1st ` %s ) = 1o )' % (E, IP('Q')))], 'mtbid',
              '( %s -> -. Q e. Prime )' % E)
    rhse = w.s([npr], 'intn3an2d', '( %s -> -. %s )' % (E, RHSB('Q')))
    ce = w.s([lhse, rhse], '2falsed', '( %s -> ( %s = 1o <-> %s ) )' % (E, KEEP('Q'), RHSB('Q')))
    cc = w.s([cd, ce], 'pm2.61dan', '( %s -> ( %s = 1o <-> %s ) )' % (C, KEEP('Q'), RHSB('Q')))
    # case -. Z < Q
    G = '( %s /\\ -. Z < Q )' % A
    kg = w.s([w.s([], 'simpr', '( %s -> -. Z < Q )' % G)], 'iffalsed', '( %s -> %s = (/) )' % (G, KEEP('Q')))
    zn1g = zne1o(w, G)
    lhsg = w.s([w.s([kg], 'eqeq1d', '( %s -> ( %s = 1o <-> (/) = 1o ) )' % (G, KEEP('Q'))), zn1g], 'mtbird',
               '( %s -> -. %s = 1o )' % (G, KEEP('Q')))
    rhsg = w.s([w.s([], 'simpr', '( %s -> -. Z < Q )' % G)], 'intn3an1d', '( %s -> -. %s )' % (G, RHSB('Q')))
    cg = w.s([lhsg, rhsg], '2falsed', '( %s -> ( %s = 1o <-> %s ) )' % (G, KEEP('Q'), RHSB('Q')))
    w.qed([cc, cg], 'pm2.61dan', '( %s -> ( %s = 1o <-> %s ) )' % (A, KEEP('Q'), RHSB('Q')))
    run(w)

# ================================================================= resgomem
OUT = '( Z e. NN0 /\\ Y e. NN )'
QU = [('q', 'NN'), ('x', 'NN0')]
BODY = '( x e. ran %s <-> ( ( q <_ x /\\ x < ( q + f ) ) /\\ %s ) )' % (R1('q', 'f'), RHSB('x'))

def _b(w, ctx, goal):
    A = ctx.A
    zz = w.s([w.s([ctx.out], 'simpld', '( %s -> Z e. NN0 )' % A)], 'id', '( %s -> Z e. NN0 )' % A)
    w.lines.pop()
    qq = ctx.v[0]; xx = ctx.v[1]
    v = w.s([w.s([ctx.out, qq], 'jca', '( %s -> ( %s /\\ q e. NN ) )' % (A, OUT)), w.inst('resgo0')], 'syl',
            '( %s -> %s = <. (/) , 0 >. )' % (A, RG('q', '0')))
    p1 = prj(w, A, RG('q', '0'), v, '(/)', '0', 1,
             aex=w.s([w.s([], '0ex', '(/) e. _V')], 'a1i', '( %s -> (/) e. _V )' % A),
             bex=w.s([w.s([], 'c0ex', '0 e. _V')], 'a1i', '( %s -> 0 e. _V )' % A))
    rn0s = w.s([w.s([p1], 'rneqd', '( %s -> ran %s = ran (/) )' % (A, R1('q', '0'))),
                w.s([w.s([], 'rn0', 'ran (/) = (/)')], 'a1i', '( %s -> ran (/) = (/) )' % A)], 'eqtrd',
               '( %s -> ran %s = (/) )' % (A, R1('q', '0')))
    nel = w.s([w.s([rn0s], 'eleq2d', '( %s -> ( x e. ran %s <-> x e. (/) ) )' % (A, R1('q', '0'))),
               w.s([w.s([], 'noel', '-. x e. (/)')], 'a1i', '( %s -> -. x e. (/) )' % A)], 'mtbird',
              '( %s -> -. x e. ran %s )' % (A, R1('q', '0')))
    B = '( %s /\\ ( q <_ x /\\ x < ( q + 0 ) ) )' % A
    qr = w.s([w.s([qq], 'adantr', '( %s -> q e. NN )' % B)], 'nnred', '( %s -> q e. RR )' % B)
    xr = w.s([w.s([xx], 'adantr', '( %s -> x e. NN0 )' % B)], 'nn0red', '( %s -> x e. RR )' % B)
    h1 = w.s([w.s([], 'simpr', '( %s -> ( q <_ x /\\ x < ( q + 0 ) ) )' % B)], 'simpld', '( %s -> q <_ x )' % B)
    h2 = w.s([w.s([], 'simpr', '( %s -> ( q <_ x /\\ x < ( q + 0 ) ) )' % B)], 'simprd', '( %s -> x < ( q + 0 ) )' % B)
    nle = w.s([w.s([xr, qr], 'ltnled', '( %s -> ( x < q <-> -. q <_ x ) )' % B),
               lin.linarith(w, B, [h2], 'x < q', leaves={'q': qr, 'x': xr})], 'mpbid', '( %s -> -. q <_ x )' % B)
    nfz = w.s([h1, nle], 'pm2.65da', '( %s -> -. ( q <_ x /\\ x < ( q + 0 ) ) )' % A)
    rn = w.s([nfz], 'intnanrd', '( %s -> -. ( ( q <_ x /\\ x < ( q + 0 ) ) /\\ %s ) )' % (A, RHSB('x')))
    return w.s([nel, rn], '2falsed', '( %s -> %s )' % (A, goal))

def _s(w, ctx, goal):
    A = ctx.A
    r = ctx.rn
    qq = ctx.v[0]; xx = ctx.v[1]; ff = ctx.fuel; out = ctx.out
    qn0 = w.s([qq], 'nnnn0d', '( %s -> q e. NN0 )' % A)
    qz = w.s([qq], 'nnzd', '( %s -> q e. ZZ )' % A)
    xz = w.s([xx], 'nn0zd', '( %s -> x e. ZZ )' % A)
    qr = w.s([qq], 'nnred', '( %s -> q e. RR )' % A)
    xr = w.s([xx], 'nn0red', '( %s -> x e. RR )' % A)
    fr = w.s([ff], 'nn0red', '( %s -> F e. RR )' % A)
    f0 = w.s([ff], 'nn0ge0d', '( %s -> 0 <_ F )' % A)
    q1 = w.s([qq, w.inst('peano2nn')], 'syl', '( %s -> ( q + 1 ) e. NN )' % A)
    rcl = w.s([w.s([w.s([out, q1], 'jca', '( %s -> ( %s /\\ ( q + 1 ) e. NN ) )' % (A, OUT)), ff, w.inst('resgocl')], 'syl2anc',
                   '( %s -> %s e. ( Word NN0 X. NN0 ) )' % (A, RG('( q + 1 )', 'F'))), w.inst('xp1st')], 'syl',
              '( %s -> %s e. Word NN0 )' % (A, R1('( q + 1 )', 'F')))
    R1F = R1('( q + 1 )', 'F')
    THEN = 'if ( %s = 1o , ( <" q "> ++ %s ) , %s )' % (KEEP('q'), R1F, R1F)
    SUM = '( ( ( %s + ( 2nd ` %s ) ) + ( 2nd ` %s ) ) + 1 )' % ('( 2nd ` %s )' % RG('( q + 1 )', 'F'), IP('q'), SM('q'))
    val = w.s([w.s([out, qq], 'jca', '( %s -> ( %s /\\ q e. NN ) )' % (A, OUT)), ff, w.inst('resgop1')], 'syl2anc',
              '( %s -> %s = <. %s , %s >. )' % (A, RG('q', '( F + 1 )'), THEN, SUM))
    s1c = w.s([qn0, w.inst('s1cl')], 'syl', '( %s -> <" q "> e. Word NN0 )' % A)
    catw = w.s([s1c, rcl, w.inst('ccatcl')], 'syl2anc', '( %s -> ( <" q "> ++ %s ) e. Word NN0 )' % (A, R1F))
    thw = w.s([catw, rcl], 'ifcld', '( %s -> %s e. Word NN0 )' % (A, THEN))
    p1 = prj(w, A, RG('q', '( F + 1 )'), val, THEN, SUM, 1,
             aex=w.s([thw], 'elexd', '( %s -> %s e. _V )' % (A, THEN)),
             bex=w.s([w.s([], 'ovex', '%s e. _V' % SUM)], 'a1i', '( %s -> %s e. _V )' % (A, SUM)))
    ihb = subst(subst(subst(BODY, 'f', 'F'), 'q', r[0]), 'x', r[1])
    ihq, _ = instn(w, A, ctx.ih, [(r[0], 'NN'), (r[1], 'NN0')], ihb, ['( q + 1 )', 'x'], [q1, xx])
    keepbi = w.s([w.s([out, qq], 'jca', '( %s -> ( %s /\\ q e. NN ) )' % (A, OUT)), w.inst('resgokeep')], 'syl',
                 '( %s -> ( %s = 1o <-> %s ) )' % (A, KEEP('q'), RHSB('q')))
    idst = w.s([], 'id', '( x = q -> x = q )')
    sbxq, nb = w.wcongr(RHSB('x'), {'x': 'q'}, 'x = q', {'x': idst})
    assert nb == RHSB('q'), '\n%s\n%s' % (nb, RHSB('q'))
    GR = '( ( q <_ x /\\ x < ( q + ( F + 1 ) ) ) /\\ %s )' % RHSB('x')
    IHR = '( ( ( q + 1 ) <_ x /\\ x < ( ( q + 1 ) + F ) ) /\\ %s )' % RHSB('x')
    # ----------------------------------------------------- keep
    K = '( %s /\\ %s = 1o )' % (A, KEEP('q'))
    k = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (K, f))
    ke = w.s([w.s([], 'simpr', '( %s -> %s = 1o )' % (K, KEEP('q')))], 'iftrued',
             '( %s -> %s = ( <" q "> ++ %s ) )' % (K, THEN, R1F))
    rk = w.s([k(p1, '%s = %s' % (R1('q', '( F + 1 )'), THEN)), ke], 'eqtrd',
             '( %s -> %s = ( <" q "> ++ %s ) )' % (K, R1('q', '( F + 1 )'), R1F))
    elkj = w.s([w.s([k(qn0, 'q e. NN0'), k(rcl, '%s e. Word NN0' % R1F)], 'jca',
                    '( %s -> ( q e. NN0 /\\ %s e. Word NN0 ) )' % (K, R1F)), k(xx, 'x e. NN0')], 'jca',
               '( %s -> ( ( q e. NN0 /\\ %s e. Word NN0 ) /\\ x e. NN0 ) )' % (K, R1F))
    elk = w.s([elkj, w.inst('algelcs')], 'syl',
              '( %s -> ( x e. ran ( <" q "> ++ %s ) <-> ( x = q \\/ x e. ran %s ) ) )' % (K, R1F, R1F))
    lhsk = w.s([w.s([rk], 'rneqd', '( %s -> ran %s = ran ( <" q "> ++ %s ) )' % (K, R1('q', '( F + 1 )'), R1F))], 'eleq2d',
               '( %s -> ( x e. ran %s <-> x e. ran ( <" q "> ++ %s ) ) )' % (K, R1('q', '( F + 1 )'), R1F))
    lhsk2 = w.s([lhsk, elk], 'bitrd',
                '( %s -> ( x e. ran %s <-> ( x = q \\/ x e. ran %s ) ) )' % (K, R1('q', '( F + 1 )'), R1F))
    #   forward: x = q
    KQ = '( %s /\\ x = q )' % K
    kq = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (KQ, f))
    xeq = w.s([], 'simpr', '( %s -> x = q )' % KQ)
    rhsq = w.s([kq(k(keepbi, '( %s = 1o <-> %s )' % (KEEP('q'), RHSB('q'))), '( %s = 1o <-> %s )' % (KEEP('q'), RHSB('q'))),
                kq(w.s([], 'simpr', '( %s -> %s = 1o )' % (K, KEEP('q'))), '%s = 1o' % KEEP('q'))], 'mpbid',
               '( %s -> %s )' % (KQ, RHSB('q')))
    rhsx = w.s([rhsq, w.s([xeq, w.s([sbxq], 'a1i', '( %s -> ( x = q -> ( %s <-> %s ) ) )' % (KQ, RHSB('x'), RHSB('q')))], 'mpd',
                          '( %s -> ( %s <-> %s ) )' % (KQ, RHSB('x'), RHSB('q')))], 'mpbird', '( %s -> %s )' % (KQ, RHSB('x')))
    aq = lin.linarith(w, KQ, [w.s([xeq], 'eqcomd', '( %s -> q = x )' % KQ)], 'q <_ x',
                      leaves={'q': kq(k(qr, 'q e. RR'), 'q e. RR'), 'x': kq(k(xr, 'x e. RR'), 'x e. RR')})
    aq2 = lin.linarith(w, KQ, [kq(k(f0, '0 <_ F'), '0 <_ F'), w.s([xeq], 'eqcomd', '( %s -> q = x )' % KQ)],
                       'x < ( q + ( F + 1 ) )',
                       leaves={'q': kq(k(qr, 'q e. RR'), 'q e. RR'), 'x': kq(k(xr, 'x e. RR'), 'x e. RR'),
                               'F': kq(k(fr, 'F e. RR'), 'F e. RR')})
    gq = w.s([w.s([aq, aq2], 'jca', '( %s -> ( q <_ x /\\ x < ( q + ( F + 1 ) ) ) )' % KQ), rhsx], 'jca',
             '( %s -> %s )' % (KQ, GR))
    #   forward: x in the tail
    KT = '( %s /\\ x e. ran %s )' % (K, R1F)
    kt = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (KT, f))
    ihv = w.s([w.s([], 'simpr', '( %s -> x e. ran %s )' % (KT, R1F)),
               kt(k(ihq, '( x e. ran %s <-> %s )' % (R1F, IHR)), '( x e. ran %s <-> %s )' % (R1F, IHR))], 'mpbid',
              '( %s -> %s )' % (KT, IHR))
    ih1 = w.s([w.s([ihv], 'simpld', '( %s -> ( ( q + 1 ) <_ x /\\ x < ( ( q + 1 ) + F ) ) )' % KT)], 'simpld',
              '( %s -> ( q + 1 ) <_ x )' % KT)
    ih2 = w.s([w.s([ihv], 'simpld', '( %s -> ( ( q + 1 ) <_ x /\\ x < ( ( q + 1 ) + F ) ) )' % KT)], 'simprd',
              '( %s -> x < ( ( q + 1 ) + F ) )' % KT)
    lv = {'q': kt(k(qr, 'q e. RR'), 'q e. RR'), 'x': kt(k(xr, 'x e. RR'), 'x e. RR'), 'F': kt(k(fr, 'F e. RR'), 'F e. RR')}
    at1 = lin.linarith(w, KT, [ih1], 'q <_ x', leaves=lv)
    at2 = lin.linarith(w, KT, [ih2], 'x < ( q + ( F + 1 ) )', leaves=lv)
    gt = w.s([w.s([at1, at2], 'jca', '( %s -> ( q <_ x /\\ x < ( q + ( F + 1 ) ) ) )' % KT),
              w.s([ihv], 'simprd', '( %s -> %s )' % (KT, RHSB('x')))], 'jca', '( %s -> %s )' % (KT, GR))
    fwdk = w.s([w.s([gq], 'ex', '( %s -> ( x = q -> %s ) )' % (K, GR)),
                w.s([gt], 'ex', '( %s -> ( x e. ran %s -> %s ) )' % (K, R1F, GR))], 'jaod',
               '( %s -> ( ( x = q \\/ x e. ran %s ) -> %s ) )' % (K, R1F, GR))
    #   backward
    KB = '( %s /\\ %s )' % (K, GR)
    kb = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (KB, f))
    b1 = w.s([w.s([w.s([], 'simpr', '( %s -> %s )' % (KB, GR))], 'simpld',
                  '( %s -> ( q <_ x /\\ x < ( q + ( F + 1 ) ) ) )' % KB)], 'simpld', '( %s -> q <_ x )' % KB)
    b2 = w.s([w.s([w.s([], 'simpr', '( %s -> %s )' % (KB, GR))], 'simpld',
                  '( %s -> ( q <_ x /\\ x < ( q + ( F + 1 ) ) ) )' % KB)], 'simprd',
             '( %s -> x < ( q + ( F + 1 ) ) )' % KB)
    b3 = w.s([w.s([], 'simpr', '( %s -> %s )' % (KB, GR))], 'simprd', '( %s -> %s )' % (KB, RHSB('x')))
    KBN = '( %s /\\ -. x = q )' % KB
    kbn = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (KBN, f))
    xne = w.s([w.s([], 'simpr', '( %s -> -. x = q )' % KBN), w.inst('neqned')], 'syl', '( %s -> x =/= q )' % KBN)
    lt = w.s([w.s([kbn(kb(k(qr, 'q e. RR'), 'q e. RR'), 'q e. RR'), kbn(kb(k(xr, 'x e. RR'), 'x e. RR'), 'x e. RR')], 'ltlend',
                  '( %s -> ( q < x <-> ( q <_ x /\\ x =/= q ) ) )' % KBN),
              w.s([kbn(b1, 'q <_ x'), xne], 'jca', '( %s -> ( q <_ x /\\ x =/= q ) )' % KBN)], 'mpbird',
             '( %s -> q < x )' % KBN)
    p1le = w.s([w.s([w.s([kbn(kb(k(qz, 'q e. ZZ'), 'q e. ZZ'), 'q e. ZZ'), kbn(kb(k(xz, 'x e. ZZ'), 'x e. ZZ'), 'x e. ZZ')], 'jca',
                         '( %s -> ( q e. ZZ /\\ x e. ZZ ) )' % KBN), w.inst('zltp1le')], 'syl',
                    '( %s -> ( q < x <-> ( q + 1 ) <_ x ) )' % KBN), lt], 'mpbid', '( %s -> ( q + 1 ) <_ x )' % KBN)
    lv2 = {'q': kbn(kb(k(qr, 'q e. RR'), 'q e. RR'), 'q e. RR'), 'x': kbn(kb(k(xr, 'x e. RR'), 'x e. RR'), 'x e. RR'),
           'F': kbn(kb(k(fr, 'F e. RR'), 'F e. RR'), 'F e. RR')}
    p2lt = lin.linarith(w, KBN, [kbn(b2, 'x < ( q + ( F + 1 ) )')], 'x < ( ( q + 1 ) + F )', leaves=lv2)
    inr = w.s([w.s([w.s([p1le, p2lt], 'jca', '( %s -> ( ( q + 1 ) <_ x /\\ x < ( ( q + 1 ) + F ) ) )' % KBN),
                    kbn(b3, RHSB('x'))], 'jca', '( %s -> %s )' % (KBN, IHR)),
               kbn(kb(k(ihq, '( x e. ran %s <-> %s )' % (R1F, IHR)), '( x e. ran %s <-> %s )' % (R1F, IHR)),
                   '( x e. ran %s <-> %s )' % (R1F, IHR))], 'mpbird', '( %s -> x e. ran %s )' % (KBN, R1F))
    dis = w.s([w.s([inr], 'olcd', '( %s -> ( x = q \\/ x e. ran %s ) )' % (KBN, R1F)),
               w.s([w.s([], 'simpr', '( ( %s /\\ x = q ) -> x = q )' % KB)], 'orcd',
                   '( ( %s /\\ x = q ) -> ( x = q \\/ x e. ran %s ) )' % (KB, R1F))], 'pm2.61dan',
              '( %s -> ( x = q \\/ x e. ran %s ) )' % (KB, R1F))
    bwdk = w.s([dis], 'ex', '( %s -> ( %s -> ( x = q \\/ x e. ran %s ) ) )' % (K, GR, R1F))
    gk = w.s([lhsk2, w.s([fwdk, bwdk], 'impbid', '( %s -> ( ( x = q \\/ x e. ran %s ) <-> %s ) )' % (K, R1F, GR))], 'bitrd',
             '( %s -> ( x e. ran %s <-> %s ) )' % (K, R1('q', '( F + 1 )'), GR))
    # ----------------------------------------------------- drop
    N = '( %s /\\ -. %s = 1o )' % (A, KEEP('q'))
    n = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (N, f))
    ne = w.s([w.s([], 'simpr', '( %s -> -. %s = 1o )' % (N, KEEP('q')))], 'iffalsed', '( %s -> %s = %s )' % (N, THEN, R1F))
    rnn = w.s([n(p1, '%s = %s' % (R1('q', '( F + 1 )'), THEN)), ne], 'eqtrd',
              '( %s -> %s = %s )' % (N, R1('q', '( F + 1 )'), R1F))
    lhsn = w.s([w.s([rnn], 'rneqd', '( %s -> ran %s = ran %s )' % (N, R1('q', '( F + 1 )'), R1F))], 'eleq2d',
               '( %s -> ( x e. ran %s <-> x e. ran %s ) )' % (N, R1('q', '( F + 1 )'), R1F))
    NT = '( %s /\\ %s )' % (N, IHR)
    nt = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (NT, f))
    n1 = w.s([w.s([w.s([], 'simpr', '( %s -> %s )' % (NT, IHR))], 'simpld',
                  '( %s -> ( ( q + 1 ) <_ x /\\ x < ( ( q + 1 ) + F ) ) )' % NT)], 'simpld', '( %s -> ( q + 1 ) <_ x )' % NT)
    n2 = w.s([w.s([w.s([], 'simpr', '( %s -> %s )' % (NT, IHR))], 'simpld',
                  '( %s -> ( ( q + 1 ) <_ x /\\ x < ( ( q + 1 ) + F ) ) )' % NT)], 'simprd',
             '( %s -> x < ( ( q + 1 ) + F ) )' % NT)
    lvn = {'q': nt(n(qr, 'q e. RR'), 'q e. RR'), 'x': nt(n(xr, 'x e. RR'), 'x e. RR'), 'F': nt(n(fr, 'F e. RR'), 'F e. RR')}
    nf1 = lin.linarith(w, NT, [n1], 'q <_ x', leaves=lvn)
    nf2 = lin.linarith(w, NT, [n2], 'x < ( q + ( F + 1 ) )', leaves=lvn)
    fwdn = w.s([w.s([w.s([nf1, nf2], 'jca', '( %s -> ( q <_ x /\\ x < ( q + ( F + 1 ) ) ) )' % NT),
                     w.s([w.s([], 'simpr', '( %s -> %s )' % (NT, IHR))], 'simprd', '( %s -> %s )' % (NT, RHSB('x')))], 'jca',
                    '( %s -> %s )' % (NT, GR))], 'ex', '( %s -> ( %s -> %s ) )' % (N, IHR, GR))
    NB = '( %s /\\ %s )' % (N, GR)
    nb2 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (NB, f))
    m1 = w.s([w.s([w.s([], 'simpr', '( %s -> %s )' % (NB, GR))], 'simpld',
                  '( %s -> ( q <_ x /\\ x < ( q + ( F + 1 ) ) ) )' % NB)], 'simpld', '( %s -> q <_ x )' % NB)
    m2 = w.s([w.s([w.s([], 'simpr', '( %s -> %s )' % (NB, GR))], 'simpld',
                  '( %s -> ( q <_ x /\\ x < ( q + ( F + 1 ) ) ) )' % NB)], 'simprd',
             '( %s -> x < ( q + ( F + 1 ) ) )' % NB)
    m3 = w.s([w.s([], 'simpr', '( %s -> %s )' % (NB, GR))], 'simprd', '( %s -> %s )' % (NB, RHSB('x')))
    #   x = q is impossible here
    NQ = '( %s /\\ x = q )' % NB
    nq = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (NQ, f))
    xeq2 = w.s([], 'simpr', '( %s -> x = q )' % NQ)
    rq = w.s([nq(m3, RHSB('x')), w.s([xeq2, w.s([sbxq], 'a1i', '( %s -> ( x = q -> ( %s <-> %s ) ) )' % (NQ, RHSB('x'), RHSB('q')))],
                                     'mpd', '( %s -> ( %s <-> %s ) )' % (NQ, RHSB('x'), RHSB('q')))], 'mpbid',
              '( %s -> %s )' % (NQ, RHSB('q')))
    kq1 = w.s([rq, nq(nb2(n(keepbi, '( %s = 1o <-> %s )' % (KEEP('q'), RHSB('q'))), '( %s = 1o <-> %s )' % (KEEP('q'), RHSB('q'))),
                      '( %s = 1o <-> %s )' % (KEEP('q'), RHSB('q')))], 'mpbird', '( %s -> %s = 1o )' % (NQ, KEEP('q')))
    xnq = w.s([kq1, nq(nb2(w.s([], 'simpr', '( %s -> -. %s = 1o )' % (N, KEEP('q'))), '-. %s = 1o' % KEEP('q')),
                       '-. %s = 1o' % KEEP('q'))], 'pm2.65da', '( %s -> -. x = q )' % NB)
    xne2 = w.s([xnq, w.inst('neqned')], 'syl', '( %s -> x =/= q )' % NB)
    lt2 = w.s([w.s([nb2(n(qr, 'q e. RR'), 'q e. RR'), nb2(n(xr, 'x e. RR'), 'x e. RR')], 'ltlend',
                   '( %s -> ( q < x <-> ( q <_ x /\\ x =/= q ) ) )' % NB),
               w.s([m1, xne2], 'jca', '( %s -> ( q <_ x /\\ x =/= q ) )' % NB)], 'mpbird', '( %s -> q < x )' % NB)
    pp1 = w.s([w.s([w.s([nb2(n(qz, 'q e. ZZ'), 'q e. ZZ'), nb2(n(xz, 'x e. ZZ'), 'x e. ZZ')], 'jca',
                        '( %s -> ( q e. ZZ /\\ x e. ZZ ) )' % NB), w.inst('zltp1le')], 'syl',
                   '( %s -> ( q < x <-> ( q + 1 ) <_ x ) )' % NB), lt2], 'mpbid', '( %s -> ( q + 1 ) <_ x )' % NB)
    lvb = {'q': nb2(n(qr, 'q e. RR'), 'q e. RR'), 'x': nb2(n(xr, 'x e. RR'), 'x e. RR'), 'F': nb2(n(fr, 'F e. RR'), 'F e. RR')}
    pp2 = lin.linarith(w, NB, [m2], 'x < ( ( q + 1 ) + F )', leaves=lvb)
    bwdn = w.s([w.s([w.s([pp1, pp2], 'jca', '( %s -> ( ( q + 1 ) <_ x /\\ x < ( ( q + 1 ) + F ) ) )' % NB), m3], 'jca',
                    '( %s -> %s )' % (NB, IHR))], 'ex', '( %s -> ( %s -> %s ) )' % (N, GR, IHR))
    gn = w.s([lhsn, w.s([n(ihq, '( x e. ran %s <-> %s )' % (R1F, IHR)),
                         w.s([fwdn, bwdn], 'impbid', '( %s -> ( %s <-> %s ) )' % (N, IHR, GR))], 'bitrd',
                        '( %s -> ( x e. ran %s <-> %s ) )' % (N, R1F, GR))], 'bitrd',
             '( %s -> ( x e. ran %s <-> %s ) )' % (N, R1('q', '( F + 1 )'), GR))
    return w.s([gk, gn], 'pm2.61dan', '( %s -> %s )' % (A, goal))

def _i(w):
    A = '( ( Z e. NN0 /\\ Y e. NN /\\ Q e. NN ) /\\ ( F e. NN0 /\\ X e. NN0 ) )'
    zz = w.s([], 'simpl1', '( %s -> Z e. NN0 )' % A)
    yy = w.s([], 'simpl2', '( %s -> Y e. NN )' % A)
    qq = w.s([], 'simpl3', '( %s -> Q e. NN )' % A)
    ff = w.s([], 'simprl', '( %s -> F e. NN0 )' % A)
    xx = w.s([], 'simprr', '( %s -> X e. NN0 )' % A)
    PH = qphi(OUT, QU, subst(BODY, 'f', 'F'))
    ral = w.s([w.s([ff, w.inst('resgomeml')], 'syl', '( %s -> %s )' % (A, PH)),
               w.s([zz, yy], 'jca', '( %s -> %s )' % (A, OUT))], 'mpd',
              '( %s -> %s )' % (A, quantify(QU, ['q', 'x'], subst(BODY, 'f', 'F'))))
    st, bd = instn(w, A, ral, QU, subst(BODY, 'f', 'F'), ['Q', 'X'], [qq, xx])
    w.lines[-1] = w.lines[-1].replace('%s:' % st, 'qed:', 1)

qfuel(run, 'resgomem', OUT, QU, BODY, _b, _s, instfn=_i, only=only,
      desc='Membership in the reservoir loop (Lean: resGo_mem).')

# ================================================================= resgondp
BODY2 = "Fun `' %s" % R1('q', 'f')

def _b2(w, ctx, goal):
    A = ctx.A
    v = w.s([w.s([ctx.out, ctx.v[0]], 'jca', '( %s -> ( %s /\\ q e. NN ) )' % (A, OUT)), w.inst('resgo0')], 'syl',
            '( %s -> %s = <. (/) , 0 >. )' % (A, RG('q', '0')))
    p1 = prj(w, A, RG('q', '0'), v, '(/)', '0', 1,
             aex=w.s([w.s([], '0ex', '(/) e. _V')], 'a1i', '( %s -> (/) e. _V )' % A),
             bex=w.s([w.s([], 'c0ex', '0 e. _V')], 'a1i', '( %s -> 0 e. _V )' % A))
    bi = w.s([w.s([p1], 'cnveqd', "( %s -> `' %s = `' (/) )" % (A, R1('q', '0')))], 'funeqd',
             "( %s -> ( Fun `' %s <-> Fun `' (/) ) )" % (A, R1('q', '0')))
    return w.s([w.s([w.s([], 'algndp0', "Fun `' (/)")], 'a1i', "( %s -> Fun `' (/) )" % A), bi], 'mpbird',
               '( %s -> %s )' % (A, goal))

def _s2(w, ctx, goal):
    A = ctx.A
    r = ctx.rn
    qq = ctx.v[0]; ff = ctx.fuel; out = ctx.out
    qn0 = w.s([qq], 'nnnn0d', '( %s -> q e. NN0 )' % A)
    qr = w.s([qq], 'nnred', '( %s -> q e. RR )' % A)
    q1 = w.s([qq, w.inst('peano2nn')], 'syl', '( %s -> ( q + 1 ) e. NN )' % A)
    R1F = R1('( q + 1 )', 'F')
    rcl = w.s([w.s([w.s([out, q1], 'jca', '( %s -> ( %s /\\ ( q + 1 ) e. NN ) )' % (A, OUT)), ff, w.inst('resgocl')], 'syl2anc',
                   '( %s -> %s e. ( Word NN0 X. NN0 ) )' % (A, RG('( q + 1 )', 'F'))), w.inst('xp1st')], 'syl',
              '( %s -> %s e. Word NN0 )' % (A, R1F))
    THEN = 'if ( %s = 1o , ( <" q "> ++ %s ) , %s )' % (KEEP('q'), R1F, R1F)
    SUM = '( ( ( %s + ( 2nd ` %s ) ) + ( 2nd ` %s ) ) + 1 )' % ('( 2nd ` %s )' % RG('( q + 1 )', 'F'), IP('q'), SM('q'))
    val = w.s([w.s([out, qq], 'jca', '( %s -> ( %s /\\ q e. NN ) )' % (A, OUT)), ff, w.inst('resgop1')], 'syl2anc',
              '( %s -> %s = <. %s , %s >. )' % (A, RG('q', '( F + 1 )'), THEN, SUM))
    s1c = w.s([qn0, w.inst('s1cl')], 'syl', '( %s -> <" q "> e. Word NN0 )' % A)
    catw = w.s([s1c, rcl, w.inst('ccatcl')], 'syl2anc', '( %s -> ( <" q "> ++ %s ) e. Word NN0 )' % (A, R1F))
    thw = w.s([catw, rcl], 'ifcld', '( %s -> %s e. Word NN0 )' % (A, THEN))
    p1 = prj(w, A, RG('q', '( F + 1 )'), val, THEN, SUM, 1,
             aex=w.s([thw], 'elexd', '( %s -> %s e. _V )' % (A, THEN)),
             bex=w.s([w.s([], 'ovex', '%s e. _V' % SUM)], 'a1i', '( %s -> %s e. _V )' % (A, SUM)))
    ihb = subst(subst(BODY2, 'f', 'F'), 'q', r[0])
    ihq, _ = instn(w, A, ctx.ih, [(r[0], 'NN')], ihb, ['( q + 1 )'], [q1])
    # q is not already in the tail
    MEM = '( ( ( q + 1 ) <_ q /\\ q < ( ( q + 1 ) + F ) ) /\\ %s )' % RHSB('q')
    zz = w.s([out], 'simpld', '( %s -> Z e. NN0 )' % A)
    yy = w.s([out], 'simprd', '( %s -> Y e. NN )' % A)
    memb = w.s([w.s([w.s([zz, yy, q1], '3jca', '( %s -> ( Z e. NN0 /\\ Y e. NN /\\ ( q + 1 ) e. NN ) )' % A),
                     w.s([ff, qn0], 'jca', '( %s -> ( F e. NN0 /\\ q e. NN0 ) )' % A)], 'jca',
                    '( %s -> ( ( Z e. NN0 /\\ Y e. NN /\\ ( q + 1 ) e. NN ) /\\ ( F e. NN0 /\\ q e. NN0 ) ) )' % A),
                w.inst('resgomem')], 'syl', '( %s -> ( q e. ran %s <-> %s ) )' % (A, R1F, MEM))
    nle = w.s([w.s([qr, w.s([qr, w.inst('peano2re')], 'syl', '( %s -> ( q + 1 ) e. RR )' % A)], 'ltnled',
                   '( %s -> ( q < ( q + 1 ) <-> -. ( q + 1 ) <_ q ) )' % A),
               w.s([qr], 'ltp1d', '( %s -> q < ( q + 1 ) )' % A)], 'mpbid', '( %s -> -. ( q + 1 ) <_ q )' % A)
    nmem = w.s([memb, w.s([w.s([nle], 'intnanrd', '( %s -> -. ( ( q + 1 ) <_ q /\\ q < ( ( q + 1 ) + F ) ) )' % A)], 'intnanrd',
                          '( %s -> -. %s )' % (A, MEM))], 'mtbird', '( %s -> -. q e. ran %s )' % (A, R1F))
    # case keep
    K = '( %s /\\ %s = 1o )' % (A, KEEP('q'))
    k = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (K, f))
    ke = w.s([w.s([], 'simpr', '( %s -> %s = 1o )' % (K, KEEP('q')))], 'iftrued',
             '( %s -> %s = ( <" q "> ++ %s ) )' % (K, THEN, R1F))
    rk = w.s([k(p1, '%s = %s' % (R1('q', '( F + 1 )'), THEN)), ke], 'eqtrd',
             '( %s -> %s = ( <" q "> ++ %s ) )' % (K, R1('q', '( F + 1 )'), R1F))
    ndc = w.s([k(qn0, 'q e. NN0'), k(rcl, '%s e. Word NN0' % R1F), w.inst('algndpcs')], 'syl2anc',
              "( %s -> ( Fun `' ( <\" q \"> ++ %s ) <-> ( -. q e. ran %s /\\ Fun `' %s ) ) )" % (K, R1F, R1F, R1F))
    fuc = w.s([w.s([k(nmem, '-. q e. ran %s' % R1F), k(ihq, "Fun `' %s" % R1F)], 'jca',
                   "( %s -> ( -. q e. ran %s /\\ Fun `' %s ) )" % (K, R1F, R1F)), ndc], 'mpbird',
              "( %s -> Fun `' ( <\" q \"> ++ %s ) )" % (K, R1F))
    gk = w.s([fuc, w.s([w.s([rk], 'cnveqd', "( %s -> `' %s = `' ( <\" q \"> ++ %s ) )" % (K, R1('q', '( F + 1 )'), R1F))], 'funeqd',
                       "( %s -> ( Fun `' %s <-> Fun `' ( <\" q \"> ++ %s ) ) )" % (K, R1('q', '( F + 1 )'), R1F))], 'mpbird',
             '( %s -> %s )' % (K, subst(BODY2, 'f', '( F + 1 )')))
    # case drop
    N = '( %s /\\ -. %s = 1o )' % (A, KEEP('q'))
    n = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (N, f))
    ne = w.s([w.s([], 'simpr', '( %s -> -. %s = 1o )' % (N, KEEP('q')))], 'iffalsed', '( %s -> %s = %s )' % (N, THEN, R1F))
    rn2 = w.s([n(p1, '%s = %s' % (R1('q', '( F + 1 )'), THEN)), ne], 'eqtrd',
              '( %s -> %s = %s )' % (N, R1('q', '( F + 1 )'), R1F))
    gn = w.s([n(ihq, "Fun `' %s" % R1F),
              w.s([w.s([rn2], 'cnveqd', "( %s -> `' %s = `' %s )" % (N, R1('q', '( F + 1 )'), R1F))], 'funeqd',
                  "( %s -> ( Fun `' %s <-> Fun `' %s ) )" % (N, R1('q', '( F + 1 )'), R1F))], 'mpbird',
             '( %s -> %s )' % (N, subst(BODY2, 'f', '( F + 1 )')))
    return w.s([gk, gn], 'pm2.61dan', '( %s -> %s )' % (A, goal))

def _i2(w):
    A = '( ( Z e. NN0 /\\ Y e. NN ) /\\ ( Q e. NN /\\ F e. NN0 ) )'
    out = w.s([], 'simpl', '( %s -> %s )' % (A, OUT))
    qq = w.s([], 'simprl', '( %s -> Q e. NN )' % A)
    ff = w.s([], 'simprr', '( %s -> F e. NN0 )' % A)
    PH = qphi(OUT, [('q', 'NN')], subst(BODY2, 'f', 'F'))
    ral = w.s([w.s([ff, w.inst('resgondpl')], 'syl', '( %s -> %s )' % (A, PH)), out], 'mpd',
              '( %s -> %s )' % (A, quantify([('q', 'NN')], ['q'], subst(BODY2, 'f', 'F'))))
    st, bd = instn(w, A, ral, [('q', 'NN')], subst(BODY2, 'f', 'F'), ['Q'], [qq])
    w.lines[-1] = w.lines[-1].replace('%s:' % st, 'qed:', 1)

qfuel(run, 'resgondp', OUT, [('q', 'NN')], BODY2, _b2, _s2, instfn=_i2, only=only,
      desc='The reservoir loop is duplicate-free (Lean: resGo_nodup).')

# ================================================================= resspecw
if not only or 'resspecw' in only:
    w = W('resspecw', 'Step 2 enumerates the good primes without duplicates (Lean: reservoir_specW).')
    A = '( Z e. NN /\\ V e. NN0 /\\ Y e. NN )'
    RV = '( ( Z Reservoir V ) ` Y )'
    RGI = '( ( ( V ResGo Y ) ` 2 ) ` ( Z - 1 ) )'
    R1I = '( 1st ` %s )' % RGI
    GPW = '( ( Z goodPrimesW V ) ` Y )'
    ZM = '( Z - 1 )'
    zz = w.s([], 'simp1', '( %s -> Z e. NN )' % A)
    vv = w.s([], 'simp2', '( %s -> V e. NN0 )' % A)
    yy = w.s([], 'simp3', '( %s -> Y e. NN )' % A)
    zn0 = w.s([zz], 'nnnn0d', '( %s -> Z e. NN0 )' % A)
    zm1 = w.s([zz, w.inst('nnm1nn0')], 'syl', '( %s -> %s e. NN0 )' % (A, ZM))
    two = w.s([w.s([], '2nn', '2 e. NN')], 'a1i', '( %s -> 2 e. NN )' % A)
    val = w.s([w.s([w.s([zz, vv], 'jca', '( %s -> ( Z e. NN /\\ V e. NN0 ) )' % A), yy], 'jca',
                   '( %s -> ( ( Z e. NN /\\ V e. NN0 ) /\\ Y e. NN ) )' % A), w.inst('reservoirval')], 'syl',
              '( %s -> %s = %s )' % (A, RV, RGI))
    rcl = w.s([w.s([w.s([w.s([vv, yy], 'jca', '( %s -> ( V e. NN0 /\\ Y e. NN ) )' % A), two], 'jca',
                        '( %s -> ( ( V e. NN0 /\\ Y e. NN ) /\\ 2 e. NN ) )' % A), zm1, w.inst('resgocl')], 'syl2anc',
                   '( %s -> %s e. ( Word NN0 X. NN0 ) )' % (A, RGI)), w.inst('xp1st')], 'syl',
              '( %s -> %s e. Word NN0 )' % (A, R1I))
    ndp = w.s([w.s([w.s([vv, yy], 'jca', '( %s -> ( V e. NN0 /\\ Y e. NN ) )' % A),
                    w.s([two, zm1], 'jca', '( %s -> ( 2 e. NN /\\ %s e. NN0 ) )' % (A, ZM))], 'jca',
                   '( %s -> ( ( V e. NN0 /\\ Y e. NN ) /\\ ( 2 e. NN /\\ %s e. NN0 ) ) )' % (A, ZM)),
               w.inst('resgondp')], 'syl', "( %s -> Fun `' %s )" % (A, R1I))
    MEM = lambda x: '( ( 2 <_ %s /\\ %s < ( 2 + %s ) ) /\\ ( V < %s /\\ %s e. Prime /\\ %s ) )' % (x, x, ZM, x, x, SMTH(x))
    def gpwstep(w, B, lz, lv, ly):
        return w.s([w.s([lz, lv, w.s([ly], 'nnnn0d', '( %s -> Y e. NN0 )' % B)], '3jca',
                        '( %s -> ( Z e. NN0 /\\ V e. NN0 /\\ Y e. NN0 ) )' % B), w.inst('elgoodprimesw')], 'syl',
                   '( %s -> ( x e. %s <-> ( x e. ( 0 ... Z ) /\\ ( x e. Prime /\\ V < x /\\ %s ) ) ) )' % (B, GPW, SMTH('x')))
    # ---- ran R1I C_ GPW
    B = '( %s /\\ x e. ran %s )' % (A, R1I)
    b = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (B, f))
    xn0 = w.s([w.s([b(rcl, '%s e. Word NN0' % R1I), w.s([], 'simpr', '( %s -> x e. ran %s )' % (B, R1I))], 'jca',
                   '( %s -> ( %s e. Word NN0 /\\ x e. ran %s ) )' % (B, R1I, R1I)), w.inst('algwrdrn')], 'syl',
              '( %s -> x e. NN0 )' % B)
    memb = w.s([w.s([w.s([b(vv, 'V e. NN0'), b(yy, 'Y e. NN'), b(two, '2 e. NN')], '3jca',
                         '( %s -> ( V e. NN0 /\\ Y e. NN /\\ 2 e. NN ) )' % B),
                     w.s([b(zm1, '%s e. NN0' % ZM), xn0], 'jca', '( %s -> ( %s e. NN0 /\\ x e. NN0 ) )' % (B, ZM))], 'jca',
                    '( %s -> ( ( V e. NN0 /\\ Y e. NN /\\ 2 e. NN ) /\\ ( %s e. NN0 /\\ x e. NN0 ) ) )' % (B, ZM)),
                w.inst('resgomem')], 'syl', '( %s -> ( x e. ran %s <-> %s ) )' % (B, R1I, MEM('x')))
    got = w.s([w.s([], 'simpr', '( %s -> x e. ran %s )' % (B, R1I)), memb], 'mpbid', '( %s -> %s )' % (B, MEM('x')))
    g1 = w.s([w.s([got], 'simpld', '( %s -> ( 2 <_ x /\\ x < ( 2 + %s ) ) )' % (B, ZM))], 'simprd',
             '( %s -> x < ( 2 + %s ) )' % (B, ZM))
    g2 = w.s([got], 'simprd', '( %s -> ( V < x /\\ x e. Prime /\\ %s ) )' % (B, SMTH('x')))
    xr = w.s([xn0], 'nn0red', '( %s -> x e. RR )' % B)
    zr = w.s([b(zz, 'Z e. NN')], 'nnred', '( %s -> Z e. RR )' % B)
    xlt = lin.linarith(w, B, [g1], 'x < ( Z + 1 )', leaves={'x': xr, 'Z': zr})
    xle = w.s([xlt, w.s([w.s([w.s([xn0], 'nn0zd', '( %s -> x e. ZZ )' % B),
                              w.s([b(zn0, 'Z e. NN0')], 'nn0zd', '( %s -> Z e. ZZ )' % B)], 'jca',
                             '( %s -> ( x e. ZZ /\\ Z e. ZZ ) )' % B), w.inst('zleltp1')], 'syl',
                        '( %s -> ( x <_ Z <-> x < ( Z + 1 ) ) )' % B)], 'mpbird', '( %s -> x <_ Z )' % B)
    xfzj = w.s([w.s([xn0], 'nn0zd', '( %s -> x e. ZZ )' % B),
                w.s([w.s([], '0z', '0 e. ZZ')], 'a1i', '( %s -> 0 e. ZZ )' % B),
                w.s([b(zn0, 'Z e. NN0')], 'nn0zd', '( %s -> Z e. ZZ )' % B)], '3jca',
               '( %s -> ( x e. ZZ /\\ 0 e. ZZ /\\ Z e. ZZ ) )' % B)
    xfz = w.s([xfzj, w.inst('elfz')], 'syl', '( %s -> ( x e. ( 0 ... Z ) <-> ( 0 <_ x /\\ x <_ Z ) ) )' % B)
    xfz2 = w.s([w.s([w.s([xn0], 'nn0ge0d', '( %s -> 0 <_ x )' % B), xle], 'jca', '( %s -> ( 0 <_ x /\\ x <_ Z ) )' % B),
                xfz], 'mpbird', '( %s -> x e. ( 0 ... Z ) )' % B)
    gp = gpwstep(w, B, b(zn0, 'Z e. NN0'), b(vv, 'V e. NN0'), b(yy, 'Y e. NN'))
    inn = w.s([w.s([xfz2, w.s([w.s([g2], 'simp2d', '( %s -> x e. Prime )' % B),
                               w.s([g2], 'simp1d', '( %s -> V < x )' % B),
                               w.s([g2], 'simp3d', '( %s -> %s )' % (B, SMTH('x')))], '3jca',
                              '( %s -> ( x e. Prime /\\ V < x /\\ %s ) )' % (B, SMTH('x')))], 'jca',
                   '( %s -> ( x e. ( 0 ... Z ) /\\ ( x e. Prime /\\ V < x /\\ %s ) ) )' % (B, SMTH('x'))), gp], 'mpbird',
              '( %s -> x e. %s )' % (B, GPW))
    ss1 = w.s([w.s([inn], 'ex', '( %s -> ( x e. ran %s -> x e. %s ) )' % (A, R1I, GPW))], 'ssrdv',
              '( %s -> ran %s C_ %s )' % (A, R1I, GPW))
    # ---- GPW C_ ran R1I
    D = '( %s /\\ x e. %s )' % (A, GPW)
    d = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (D, f))
    gpd = gpwstep(w, D, d(zn0, 'Z e. NN0'), d(vv, 'V e. NN0'), d(yy, 'Y e. NN'))
    gd = w.s([w.s([], 'simpr', '( %s -> x e. %s )' % (D, GPW)), gpd], 'mpbid',
             '( %s -> ( x e. ( 0 ... Z ) /\\ ( x e. Prime /\\ V < x /\\ %s ) ) )' % (D, SMTH('x')))
    dfz = w.s([gd], 'simpld', '( %s -> x e. ( 0 ... Z ) )' % D)
    d3 = w.s([gd], 'simprd', '( %s -> ( x e. Prime /\\ V < x /\\ %s ) )' % (D, SMTH('x')))
    dxz = w.s([dfz, w.inst('elfzelz')], 'syl', '( %s -> x e. ZZ )' % D)
    dbij = w.s([dxz, w.s([w.s([], '0z', '0 e. ZZ')], 'a1i', '( %s -> 0 e. ZZ )' % D),
                w.s([d(zn0, 'Z e. NN0')], 'nn0zd', '( %s -> Z e. ZZ )' % D)], '3jca',
               '( %s -> ( x e. ZZ /\\ 0 e. ZZ /\\ Z e. ZZ ) )' % D)
    dbi = w.s([dbij, w.inst('elfz')], 'syl', '( %s -> ( x e. ( 0 ... Z ) <-> ( 0 <_ x /\\ x <_ Z ) ) )' % D)
    dle = w.s([dfz, dbi], 'mpbid', '( %s -> ( 0 <_ x /\\ x <_ Z ) )' % D)
    dxn0 = w.s([w.s([dxz, w.s([dle], 'simpld', '( %s -> 0 <_ x )' % D)], 'jca', '( %s -> ( x e. ZZ /\\ 0 <_ x ) )' % D),
                w.s([w.s([], 'elnn0z', '( x e. NN0 <-> ( x e. ZZ /\\ 0 <_ x ) )')], 'a1i',
                    '( %s -> ( x e. NN0 <-> ( x e. ZZ /\\ 0 <_ x ) ) )' % D)], 'mpbird', '( %s -> x e. NN0 )' % D)
    dge2 = w.s([w.s([w.s([d3], 'simp1d', '( %s -> x e. Prime )' % D), w.inst('prmuz2')], 'syl',
                    '( %s -> x e. ( ZZ>= ` 2 ) )' % D), w.inst('eluzle')], 'syl', '( %s -> 2 <_ x )' % D)
    dxr = w.s([dxn0], 'nn0red', '( %s -> x e. RR )' % D)
    dzr = w.s([d(zz, 'Z e. NN')], 'nnred', '( %s -> Z e. RR )' % D)
    dlt = lin.linarith(w, D, [w.s([dle], 'simprd', '( %s -> x <_ Z )' % D)], 'x < ( 2 + %s )' % ZM,
                       leaves={'x': dxr, 'Z': dzr})
    dmem = w.s([w.s([w.s([d(vv, 'V e. NN0'), d(yy, 'Y e. NN'), d(two, '2 e. NN')], '3jca',
                         '( %s -> ( V e. NN0 /\\ Y e. NN /\\ 2 e. NN ) )' % D),
                     w.s([d(zm1, '%s e. NN0' % ZM), dxn0], 'jca', '( %s -> ( %s e. NN0 /\\ x e. NN0 ) )' % (D, ZM))], 'jca',
                    '( %s -> ( ( V e. NN0 /\\ Y e. NN /\\ 2 e. NN ) /\\ ( %s e. NN0 /\\ x e. NN0 ) ) )' % (D, ZM)),
                w.inst('resgomem')], 'syl', '( %s -> ( x e. ran %s <-> %s ) )' % (D, R1I, MEM('x')))
    dinn = w.s([w.s([w.s([dge2, dlt], 'jca', '( %s -> ( 2 <_ x /\\ x < ( 2 + %s ) ) )' % (D, ZM)),
                     w.s([w.s([d3], 'simp2d', '( %s -> V < x )' % D), w.s([d3], 'simp1d', '( %s -> x e. Prime )' % D),
                          w.s([d3], 'simp3d', '( %s -> %s )' % (D, SMTH('x')))], '3jca',
                         '( %s -> ( V < x /\\ x e. Prime /\\ %s ) )' % (D, SMTH('x')))], 'jca',
                    '( %s -> %s )' % (D, MEM('x'))), dmem], 'mpbird', '( %s -> x e. ran %s )' % (D, R1I))
    ss2 = w.s([w.s([dinn], 'ex', '( %s -> ( x e. %s -> x e. ran %s ) )' % (A, GPW, R1I))], 'ssrdv',
              '( %s -> %s C_ ran %s )' % (A, GPW, R1I))
    rneq = w.s([ss1, ss2], 'eqssd', '( %s -> ran %s = %s )' % (A, R1I, GPW))
    # transport to the Reservoir form
    p1eq = w.s([val], 'fveq2d', '( %s -> ( 1st ` %s ) = %s )' % (A, RV, R1I))
    fufin = w.s([ndp, w.s([w.s([p1eq], 'cnveqd', "( %s -> `' ( 1st ` %s ) = `' %s )" % (A, RV, R1I))], 'funeqd',
                          "( %s -> ( Fun `' ( 1st ` %s ) <-> Fun `' %s ) )" % (A, RV, R1I))], 'mpbird',
                "( %s -> Fun `' ( 1st ` %s ) )" % (A, RV))
    rnfin = w.s([w.s([p1eq], 'rneqd', '( %s -> ran ( 1st ` %s ) = ran %s )' % (A, RV, R1I)), rneq], 'eqtrd',
                '( %s -> ran ( 1st ` %s ) = %s )' % (A, RV, GPW))
    w.qed([fufin, rnfin], 'jca', "( %s -> ( Fun `' ( 1st ` %s ) /\\ ran ( 1st ` %s ) = %s ) )" % (A, RV, RV, GPW))
    run(w)
