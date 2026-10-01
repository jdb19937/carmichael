"""Sortie DSH: dshvlc, the closure VL ( GR ( R ) , HL ) e. CC (z6vlcvg on the line Re w = HL with the strip
~ dshgrsd and the majorant ~ dshgrmaj ); replaces z6ectrl's use in dshdetr.
Run: MM_DB=sorties/dsh.mm MM_ENGINE=mmatch python3 tools/gen/dsh_v.py"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from dsh_b_s import *
import dshlib


def dshvlc():
    w = W('dshvlc', 'The vertical line integral of the contour integrand on ` Re w = 1/2 - Re S ` converges (~ z6vlcvg with the strip ~ dshgrsd '
          'and the majorant ~ dshgrmaj ; Lean ` integrable_Ghat_line_half ` ).')
    a = ante('dshshiftr'); f = unpack(w, a); st = mkst(w, a)
    sc = f['S e. CC']; lo = f['( ; 3 9 / ; 5 0 ) <_ ( Re ` S )']
    d = dfacts(w, a, f)
    rs = st([sc], 'recld', '( Re ` S ) e. RR')
    c2_ = c_(w, a, num.real(w, '( 1 / 2 )'), '( 1 / 2 ) e. RR')
    hlr = st([c2_, rs], 'resubcld', '%s e. RR' % CL)
    hl3 = linarith(w, a, [lo], '%s <_ 3' % CL, leaves={'( Re ` S )': rs})
    fz = {}
    fz['%s e. RR' % CL] = hlr
    fz['%s e. ( %s -cn-> CC )' % (GR('R'), DS)], _ = applyn(w, a, 'dshgrcn', {}, f)
    isc = st([st([sc], 'imcld', '( Im ` S ) e. RR')], 'recnd', '( Im ` S ) e. CC')
    ais = st([isc], 'abscld', '( abs ` ( Im ` S ) ) e. RR'); ag0 = st([isc], 'absge0d', '0 <_ ( abs ` ( Im ` S ) )')
    y5r = st([ais, one(w, a)], 'readdcld', '%s e. RR' % Y5)
    fz['%s e. RR+' % Y5] = st([y5r, linarith(w, a, [ag0], '0 < %s' % Y5, leaves={'( abs ` ( Im ` S ) )': ais})], 'elrpd', '%s e. RR+' % Y5)
    rr, ge1 = omgfacts(w, a, f['N e. NN'])
    nr = st([f['N e. NN']], 'nnred', 'N e. RR')
    three = c_(w, a, w.s([], '3re', '3 e. RR'), '3 e. RR')
    K4 = '( ; ; ; ; ; 4 0 0 0 0 0 x. %s )' % OMGN
    NA = '( N x. ( ( abs ` ( Im ` S ) ) + 3 ) )'
    lb0 = st([st([c_(w, a, num.real(w, '; ; ; ; ; 4 0 0 0 0 0'), '; ; ; ; ; 4 0 0 0 0 0 e. RR'), rr], 'remulcld', '%s e. RR' % K4),
              st([st([nr, st([ais, three], 'readdcld', '( ( abs ` ( Im ` S ) ) + 3 ) e. RR')], 'remulcld', '%s e. RR' % NA)], 'resqcld', '( %s ^ 2 ) e. RR' % NA)],
             'remulcld', '%s e. RR' % LB0)
    ZR = '( %s x. ( R ^ 3 ) )' % Z2D
    zr = st([st([d['z2rp']], 'rpred', '%s e. RR' % Z2D), st([st([f['R e. NN']], 'nnred', 'R e. RR'), c_(w, a, w.s([], '3nn0', '3 e. NN0'), '3 e. NN0')], 'reexpcld',
                                                                                      '( R ^ 3 ) e. RR')], 'remulcld', '%s e. RR' % ZR)
    x3 = st([st([d['xrp'], three], 'rpcxpcld', '( %s ^c 3 ) e. RR+' % XPD)], 'rpred', '( %s ^c 3 ) e. RR' % XPD)
    c12 = st([c_(w, a, num.real(w, '; ; ; 1 6 3 2'), '; ; ; 1 6 3 2 e. RR'), c_(w, a, num.real(w, '; ; 1 2 8'), '; ; 1 2 8 e. RR')], 'remulcld', '( ; ; ; 1 6 3 2 x. ; ; 1 2 8 ) e. RR')
    fz['%s e. RR' % M5] = st([st([c12, x3], 'remulcld', '( ( ; ; ; 1 6 3 2 x. ; ; 1 2 8 ) x. ( %s ^c 3 ) ) e. RR' % XPD), st([lb0, zr], 'remulcld', '( %s x. %s ) e. RR' % (LB0, ZR))],
                             'remulcld', '%s e. RR' % M5)
    SD = split_imp(STATEMENTS['dshgrsd'])[1]; SM = split_imp(STATEMENTS['dshgrmaj'])[1]
    gsd = w.s([], 'dshgrsd', STATEMENTS['dshgrsd']); gmj = w.s([], 'dshgrmaj', STATEMENTS['dshgrmaj'])
    # the point Z = HL + i u
    au = '( %s /\\ u e. RR )' % a; t = mkst(w, au)
    Z = '( %s + ( _i x. u ) )' % CL
    ur = t([], 'simpr', 'u e. RR')
    hlu = lift(w, hlr, au)
    zc = t([t([hlu], 'recnd', '%s e. CC' % CL), t([c_(w, au, w.s([], 'ax-icn', '_i e. CC'), '_i e. CC'), t([ur], 'recnd', 'u e. CC')], 'mulcld', '( _i x. u ) e. CC')],
           'addcld', '%s e. CC' % Z)
    rez = t([hlu, ur], 'crred', '( Re ` %s ) = %s' % (Z, CL))
    imz = t([hlu, ur], 'crimd', '( Im ` %s ) = u' % Z)
    le1 = t([hlu, t([rez], 'eqcomd', '%s = ( Re ` %s )' % (CL, Z))], 'eqled', '%s <_ ( Re ` %s )' % (CL, Z))
    le3 = t([rez, lift(w, hl3, au)], 'eqbrtrd', '( Re ` %s ) <_ 3' % Z)
    rng = t([le1, le3], 'jca', '( %s <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ 3 )' % (CL, Z, Z))
    D1 = '( ( Re ` %s ) = %s \\/ ( Re ` %s ) = 3 )' % (Z, CL, Z)
    dis = t([t([rez], 'orcd', D1)], 'orcd', '( %s \\/ %s <_ ( abs ` ( Im ` %s ) ) )' % (D1, Y5, Z))
    BSD = SD.split(' ', 5)[5][:-2] if False else None
    body = SD[len('A. z e. CC '):]
    ins, new = inst_all(w, au, t([gsd], 'adantr' if False else 'x', 'x') if False else w.s([w.s([], 'dshgrsd', STATEMENTS['dshgrsd'])], 'adantr', '( %s -> %s )' % (au, SD)),
                        'z', 'CC', body, Z, zc)
    zin = t([t([rng, dis], 'jca', split_imp(new)[0]), ins], 'mpd', '%s e. %s' % (Z, DS))
    fz['A. u e. RR %s e. %s' % (Z, DS)] = st([zin], 'ralrimiva', 'A. u e. RR %s e. %s' % (Z, DS))
    # the majorant on the line
    c2 = '( %s /\\ %s <_ ( abs ` u ) )' % (au, Y5); t2 = mkst(w, c2)
    zc2 = lift(w, zc, c2); imz2 = lift(w, imz, c2)
    aim = t2([imz2], 'fveq2d', '( abs ` ( Im ` %s ) ) = ( abs ` u )' % Z)
    y5le = t2([t2([], 'simpr', '%s <_ ( abs ` u )' % Y5), aim], 'breqtrrd', '%s <_ ( abs ` ( Im ` %s ) )' % (Y5, Z))
    bodym = SM[len('A. z e. CC '):]
    insm, newm = inst_all(w, c2, w.s([w.s([], 'dshgrmaj', STATEMENTS['dshgrmaj'])], 'adantr' if False else 'x', 'x') if False else
                          w.s([gmj], 'ad2antrr', '( %s -> %s )' % (c2, SM)), 'z', 'CC', bodym, Z, zc2)
    hyp_ = split_imp(newm)[0]
    bnd = t2([t2([lift(w, rng, c2), y5le], 'jca', hyp_), insm], 'mpd', split_imp(newm)[1])
    q1 = t2([aim], 'oveq1d', '( ( abs ` ( Im ` %s ) ) / 4 ) = ( ( abs ` u ) / 4 )' % Z)
    q2 = t2([q1], 'negeqd', '-u ( ( abs ` ( Im ` %s ) ) / 4 ) = -u ( ( abs ` u ) / 4 )' % Z)
    q3 = t2([q2], 'oveq2d', '%s = %s' % (E4('( abs ` ( Im ` %s ) )' % Z), E4('( abs ` u )')))
    q4 = t2([q3], 'oveq2d', '( %s x. %s ) = ( %s x. %s )' % (M5, E4('( abs ` ( Im ` %s ) )' % Z), M5, E4('( abs ` u )')))
    bnd2 = t2([bnd, q4], 'breqtrd', '( abs ` ( %s ` %s ) ) <_ ( %s x. %s )' % (GR('R'), Z, M5, E4('( abs ` u )')))
    MJ = '( %s <_ ( abs ` u ) -> ( abs ` ( %s ` %s ) ) <_ ( %s x. %s ) )' % (Y5, GR('R'), Z, M5, E4('( abs ` u )'))
    fz['A. u e. RR %s' % MJ] = st([t([bnd2], 'ex', MJ)], 'ralrimiva', 'A. u e. RR %s' % MJ)
    vc, vcc = applyn(w, a, 'z6vlcvg', {'C': CL, 'G': GR('R'), 'D': DS, 'M': M5, 'Y': Y5}, fz)
    from z6a_e3 import _split
    cv = st([vc], 'simpld', _split(vcc)[0])
    s = st([cv, w.inst('rlimcl')], 'syl', '%s e. CC' % VL(GR('R'), CL))
    dshlib.toqed(w, s, 'dshvlc')
    return w


if __name__ == '__main__':
    lin.FASTPATH = True
    run(dshvlc())
