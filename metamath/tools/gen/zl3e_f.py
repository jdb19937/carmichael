"""ZL3e section F: the closed form of the continuation.  `MM_DB=sorties/zl3e.mm python3 tools/gen/zl3e_f.py [LABEL...]`"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from zl3e_base import *
from cl import lift as _lift

MAIN = __name__ == '__main__'
PM, MPI = '( _pi / M )', '( M / _pi )'


def pm_facts(w, A, mn):
    cl = Closure(w, A, {'M': ('NN', mn), '_pi': ('RR+', cst(w, A, 'pirp', '_pi e. RR+'))})
    return cl, cl.mem(PM, 'RR+'), cl.mem(MPI, 'RR+')


def pm_one(w, A, cl, W_, wc):
    """( A -> ( ( ( _pi / M ) ^c W ) x. ( ( M / _pi ) ^c W ) ) = 1 )"""
    pr, mr = cl.mem(PM, 'RR'), cl.mem(MPI, 'RR')
    mc_ = D(w, A, 'mulcxpd', [pr, cl.ge0(PM), mr, cl.ge0(MPI), wc], '( ( %s x. %s ) ^c %s ) = ( ( %s ^c %s ) x. ( %s ^c %s ) )' % (PM, MPI, W_, PM, W_, MPI, W_))
    pc_, mcc = cl.mem('_pi', 'CC'), cl.mem('M', 'CC')
    one = chain(w, A, ['( %s x. %s )' % (PM, MPI), '( ( _pi x. M ) / ( M x. _pi ) )', '( ( _pi x. M ) / ( _pi x. M ) )', '1'],
                [D(w, A, 'divmuldivd', [pc_, mcc, mcc, pc_, cl.ne0('M'), cl.ne0('_pi')], '( %s x. %s ) = ( ( _pi x. M ) / ( M x. _pi ) )' % (PM, MPI)),
                 D(w, A, 'oveq2d', [D(w, A, 'mulcomd', [mcc, pc_], '( M x. _pi ) = ( _pi x. M )')], '( ( _pi x. M ) / ( M x. _pi ) ) = ( ( _pi x. M ) / ( _pi x. M ) )'),
                 D(w, A, 'dividd', [cl.mem('( _pi x. M )', 'CC'), cl.ne0('( _pi x. M )')], '( ( _pi x. M ) / ( _pi x. M ) ) = 1')])
    e = D(w, A, 'eqtrd', [D(w, A, 'oveq1d', [one], '( ( %s x. %s ) ^c %s ) = ( 1 ^c %s )' % (PM, MPI, W_, W_)), D(w, A, '1cxpd', [wc], '( 1 ^c %s ) = 1' % W_)],
          '( ( %s x. %s ) ^c %s ) = 1' % (PM, MPI, W_))
    return D(w, A, 'eqtr3d', [mc_, e], '( ( %s ^c %s ) x. ( %s ^c %s ) ) = 1' % (PM, W_, MPI, W_))


# ---------------------------------------------------------------- zl3gga
if wante('zl3gga', MAIN):
    w = W('zl3gga', '` g ( Z ) = w / ( ( M / pi ) ^ w Gamma ( w + 1 ) ) ` is the reciprocal of the Gamma factor ` ( M / pi ) ^ w Gamma ( w ) ` where ` 0 < Re w ` .')
    A, Cc = ante_e('zl3gga')
    mp = D(w, A, 'simpl', [], LE.MP); mn = D(w, A, 'simpld', [mp], 'M e. NN'); pp = D(w, A, 'simprd', [mp], 'P e. { 0 , 1 }')
    zc = D(w, A, 'simprl', [], 'Z e. CC'); w0 = D(w, A, 'simprr', [], '0 < ( Re ` %s )' % LE.WV('Z'))
    pn, pr, p0, p1 = p01(w, A, pp)
    W_ = LE.WV('Z')
    wc = D(w, A, 'halfcld', [D(w, A, 'addcld', [zc, D(w, A, 'recnd', [pr], 'P e. CC')], '( Z + P ) e. CC')], '%s e. CC' % W_)
    wdm = D(w, A, 'syl2anc', [wc, w0, w.inst('zrenn')], '%s e. ( CC \\ ( ZZ \\ NN ) )' % W_)
    G0, G1 = '( _G ` %s )' % W_, '( _G ` ( %s + 1 ) )' % W_
    g0c = D(w, A, 'syl', [wdm, w.inst('gamcl')], '%s e. CC' % G0); g0n = D(w, A, 'syl', [wdm, w.inst('gamne0')], '%s =/= 0' % G0)
    ad0 = w.s([w.s([], 'fveq2', '( %s = 0 -> ( Re ` %s ) = ( Re ` 0 ) )' % (W_, W_)), w.s([], 're0', '( Re ` 0 ) = 0')], 'eqtrdi', '( %s = 0 -> ( Re ` %s ) = 0 )' % (W_, W_))
    wne = w.s([D(w, A, 'gt0ne0d', [w0], '( Re ` %s ) =/= 0' % W_), w.s([ad0], 'necon3i', '( ( Re ` %s ) =/= 0 -> %s =/= 0 )' % (W_, W_))], 'syl', '( %s -> %s =/= 0 )' % (A, W_))
    gp1 = D(w, A, 'syl', [wdm, w.inst('gamp1')], '%s = ( %s x. %s )' % (G1, G0, W_))
    cl, pmr, mpr = pm_facts(w, A, mn)
    X, Y = '( %s ^c %s )' % (PM, W_), '( %s ^c %s )' % (MPI, W_)
    xc = D(w, A, 'cxpcld', [cl.mem(PM, 'CC'), wc], '%s e. CC' % X); yc = D(w, A, 'cxpcld', [cl.mem(MPI, 'CC'), wc], '%s e. CC' % Y)
    gw = '( %s x. %s )' % (G0, W_)
    gwc = D(w, A, 'mulcld', [g0c, wc], '%s e. CC' % gw)
    e = chain(w, A, ['( %s x. ( %s x. %s ) )' % (LE.GV('Z'), Y, G0),
                     '( ( %s x. ( %s / %s ) ) x. ( %s x. %s ) )' % (W_, X, gw, Y, G0),
                     '( ( ( %s x. %s ) / ( %s x. %s ) ) x. ( %s x. %s ) )' % (X, W_, G0, W_, Y, G0),
                     '( ( %s / %s ) x. ( %s x. %s ) )' % (X, G0, Y, G0),
                     '( ( %s / %s ) x. ( %s x. %s ) )' % (X, G0, G0, Y),
                     '( ( ( %s / %s ) x. %s ) x. %s )' % (X, G0, G0, Y),
                     '( %s x. %s )' % (X, Y), '1'],
              [D(w, A, 'oveq1d', [D(w, A, 'oveq2d', [D(w, A, 'oveq2d', [gp1], '( %s / %s ) = ( %s / %s )' % (X, G1, X, gw))], '%s = ( %s x. ( %s / %s ) )' % (LE.GV('Z'), W_, X, gw))],
                 '( %s x. ( %s x. %s ) ) = ( ( %s x. ( %s / %s ) ) x. ( %s x. %s ) )' % (LE.GV('Z'), Y, G0, W_, X, gw, Y, G0)),
               D(w, A, 'oveq1d', [D(w, A, 'eqtr4d', [D(w, A, 'divassd', [wc, xc, gwc, D(w, A, 'mulne0d', [g0c, g0n, wc, wne], '%s =/= 0' % gw)], '( ( %s x. %s ) / %s ) = ( %s x. ( %s / %s ) )' % (W_, X, gw, W_, X, gw)) and
                                                      D(w, A, 'eqcomd', [D(w, A, 'divassd', [wc, xc, gwc, D(w, A, 'mulne0d', [g0c, g0n, wc, wne], '%s =/= 0' % gw)], '( ( %s x. %s ) / %s ) = ( %s x. ( %s / %s ) )' % (W_, X, gw, W_, X, gw))],
                                                        '( %s x. ( %s / %s ) ) = ( ( %s x. %s ) / %s )' % (W_, X, gw, W_, X, gw)),
                                                      D(w, A, 'oveq1d', [D(w, A, 'mulcomd', [xc, wc], '( %s x. %s ) = ( %s x. %s )' % (X, W_, W_, X))], '( ( %s x. %s ) / %s ) = ( ( %s x. %s ) / %s )' % (X, W_, gw, W_, X, gw))],
                                    '( %s x. ( %s / %s ) ) = ( ( %s x. %s ) / %s )' % (W_, X, gw, X, W_, gw))],
                 '( ( %s x. ( %s / %s ) ) x. ( %s x. %s ) ) = ( ( ( %s x. %s ) / ( %s x. %s ) ) x. ( %s x. %s ) )' % (W_, X, gw, Y, G0, X, W_, G0, W_, Y, G0)),
               D(w, A, 'oveq1d', [D(w, A, 'divcan5rd', [xc, g0c, wc, g0n, wne], '( ( %s x. %s ) / ( %s x. %s ) ) = ( %s / %s )' % (X, W_, G0, W_, X, G0))],
                 '( ( ( %s x. %s ) / ( %s x. %s ) ) x. ( %s x. %s ) ) = ( ( %s / %s ) x. ( %s x. %s ) )' % (X, W_, G0, W_, Y, G0, X, G0, Y, G0)),
               D(w, A, 'oveq2d', [D(w, A, 'mulcomd', [yc, g0c], '( %s x. %s ) = ( %s x. %s )' % (Y, G0, G0, Y))], '( ( %s / %s ) x. ( %s x. %s ) ) = ( ( %s / %s ) x. ( %s x. %s ) )' % (X, G0, Y, G0, X, G0, G0, Y)),
               ('r', D(w, A, 'mulassd', [D(w, A, 'divcld', [xc, g0c, g0n], '( %s / %s ) e. CC' % (X, G0)), g0c, yc], '( ( ( %s / %s ) x. %s ) x. %s ) = ( ( %s / %s ) x. ( %s x. %s ) )' % (X, G0, G0, Y, X, G0, G0, Y))),
               D(w, A, 'oveq1d', [D(w, A, 'divcan1d', [xc, g0c, g0n], '( ( %s / %s ) x. %s ) = %s' % (X, G0, G0, X))], '( ( ( %s / %s ) x. %s ) x. %s ) = ( %s x. %s )' % (X, G0, G0, Y, X, Y)),
               pm_one(w, A, cl, W_, wc)])
    w.qed([e], 'idi', SE['zl3gga'])
    goe(w)


# ---------------------------------------------------------------- zl3gfr
if wante('zl3gfr', MAIN):
    w = W('zl3gfr', 'The Gamma-factor ratio: ` GAMF ( 1 - Z ) g ( Z ) = M ^ ( 1 / 2 - Z ) QQ ( P ) ( Z ) ` on ` -1 < Re Z < 1 ` ( ~ zl3igp1 ).')
    A, Cc = ante_e('zl3gfr')
    mp = D(w, A, 'simpl', [], LE.MP); mn = D(w, A, 'simpld', [mp], 'M e. NN'); pp = D(w, A, 'simprd', [mp], 'P e. { 0 , 1 }')
    zc = D(w, A, 'simpr1', [], 'Z e. CC'); zr = D(w, A, 'simpr2', [], '-u 1 < ( Re ` Z )'); zr1 = D(w, A, 'simpr3', [], '( Re ` Z ) < 1')
    pn, pr, p0, p1 = p01(w, A, pp)
    pc = D(w, A, 'recnd', [pr], 'P e. CC')
    spc, reW, imW = reim_w(w, A, 'Z', zc, pc, pr)
    W_ = LE.WV('Z'); W2 = '( ( ( 1 - Z ) + P ) / 2 )'
    two, t0 = cst(w, A, '2cn', '2 e. CC'), cst(w, A, '2ne0', '2 =/= 0')
    one = cst(w, A, 'ax-1cn', '1 e. CC')
    omz = D(w, A, 'subcld', [one, zc], '( 1 - Z ) e. CC')
    wc = D(w, A, 'divcld', [spc, two, t0], '%s e. CC' % W_)
    w2c = D(w, A, 'divcld', [D(w, A, 'addcld', [omz, pc], '( ( 1 - Z ) + P ) e. CC'), two, t0], '%s e. CC' % W2)
    cl, pmr, mpr = pm_facts(w, A, mn)
    rzr = D(w, A, 'recld', [zc], '( Re ` Z ) e. RR')
    cl.have('( Re ` Z )', 'RR', rzr); cl.have('P', 'RR', pr); cl.have('P', 'ge0', p0)
    wre = D(w, A, 'breqtrrd', [linarith(w, A, [zr, p0], '-u 1 < ( ( ( Re ` Z ) + P ) / 2 )', closure=cl), reW], '-u 1 < ( Re ` %s )' % W_)
    igp = D(w, A, 'syl2anc', [wc, wre, w.inst('zl3igp1')], '( 1/_G ` %s ) = ( %s / ( _G ` ( %s + 1 ) ) )' % (W_, W_, W_))
    QB = lambda v: '( ( _pi ^c ( %s - ( 1 / 2 ) ) ) x. ( ( _G ` ( ( ( 1 - %s ) + P ) / 2 ) ) x. ( 1/_G ` ( ( %s + P ) / 2 ) ) ) )' % (v, v, v)
    qv = fv1(w, A, 'w', 'CC', QB, 'Z', zc, 'ovex')
    PiH = '( _pi ^c ( Z - ( 1 / 2 ) ) )'
    Ga2, G1 = '( _G ` %s )' % W2, '( _G ` ( %s + 1 ) )' % W_
    RQ = '( %s x. ( %s x. ( %s / %s ) ) )' % (PiH, Ga2, W_, G1)
    qv2 = D(w, A, 'eqtrd', [qv, D(w, A, 'oveq2d', [D(w, A, 'oveq2d', [igp], '( %s x. ( 1/_G ` %s ) ) = ( %s x. ( %s / %s ) )' % (Ga2, W_, Ga2, W_, G1))],
                                                  '%s = %s' % (QB('Z'), RQ))], '( %s ` Z ) = %s' % (LE.QQ('P'), RQ))
    X, Y2, Y1 = '( %s ^c %s )' % (PM, W_), '( %s ^c %s )' % (MPI, W2), '( %s ^c %s )' % (MPI, W_)
    mpc, mpn = cl.mem(MPI, 'CC'), cl.ne0(MPI)
    hz = '( ( 1 / 2 ) - Z )'
    hzc = D(w, A, 'subcld', [cst(w, A, 'halfcn', '( 1 / 2 ) e. CC'), zc], '%s e. CC' % hz)
    rd = w.s([D(w, A, 'jca', [D(w, A, 'jca', [cl.mem('M', 'CC'), cl.ne0('M')], '( M e. CC /\\ M =/= 0 )'), D(w, A, 'jca', [cl.mem('_pi', 'CC'), cl.ne0('_pi')], '( _pi e. CC /\\ _pi =/= 0 )')],
                             '( ( M e. CC /\\ M =/= 0 ) /\\ ( _pi e. CC /\\ _pi =/= 0 ) )'), w.inst('recdiv')], 'syl', '( %s -> ( 1 / %s ) = %s )' % (A, MPI, PM))
    rp_ = D(w, A, 'eqtrd', [D(w, A, 'oveq1d', [D(w, A, 'eqcomd', [rd], '%s = ( 1 / %s )' % (PM, MPI))], '%s = ( ( 1 / %s ) ^c %s )' % (X, MPI, W_)),
                            D(w, A, 'syl2anc', [mpr, wc, w.inst('cxprec')], '( ( 1 / %s ) ^c %s ) = ( 1 / %s )' % (MPI, W_, Y1))], '%s = ( 1 / %s )' % (X, Y1))
    y1c = D(w, A, 'cxpcld', [mpc, wc], '%s e. CC' % Y1); y1n = D(w, A, 'cxpne0d', [mpc, mpn, wc], '%s =/= 0' % Y1)
    y2c = D(w, A, 'cxpcld', [mpc, w2c], '%s e. CC' % Y2)
    zdif = chain(w, A, ['( %s - %s )' % (W2, W_), '( ( ( ( 1 - Z ) + P ) - ( Z + P ) ) / 2 )', '( ( 1 - ( 2 x. Z ) ) / 2 )', hz],
                 [('r', D(w, A, 'divsubdird', [D(w, A, 'addcld', [omz, pc], '( ( 1 - Z ) + P ) e. CC'), spc, two, t0],
                         '( ( ( ( 1 - Z ) + P ) - ( Z + P ) ) / 2 ) = ( %s - %s )' % (W2, W_))),
                  D(w, A, 'oveq1d', [D(w, A, 'eqtrd', [D(w, A, 'pnpcan2d', [omz, zc, pc], '( ( ( 1 - Z ) + P ) - ( Z + P ) ) = ( ( 1 - Z ) - Z )'),
                                                        D(w, A, 'eqtrd', [D(w, A, 'subsub4d', [one, zc, zc], '( ( 1 - Z ) - Z ) = ( 1 - ( Z + Z ) )'),
                                                                          D(w, A, 'oveq2d', [D(w, A, 'eqcomd', [D(w, A, '2timesd', [zc], '( 2 x. Z ) = ( Z + Z )')], '( Z + Z ) = ( 2 x. Z )')], '( 1 - ( Z + Z ) ) = ( 1 - ( 2 x. Z ) )')],
                                                          '( ( 1 - Z ) - Z ) = ( 1 - ( 2 x. Z ) )')], '( ( ( 1 - Z ) + P ) - ( Z + P ) ) = ( 1 - ( 2 x. Z ) )')],
                    '( ( ( ( 1 - Z ) + P ) - ( Z + P ) ) / 2 ) = ( ( 1 - ( 2 x. Z ) ) / 2 )'),
                  D(w, A, 'eqtrd', [D(w, A, 'divsubdird', [one, D(w, A, 'mulcld', [two, zc], '( 2 x. Z ) e. CC'), two, t0], '( ( 1 - ( 2 x. Z ) ) / 2 ) = ( ( 1 / 2 ) - ( ( 2 x. Z ) / 2 ) )'),
                                    D(w, A, 'oveq2d', [D(w, A, 'divcan3d', [zc, two, t0], '( ( 2 x. Z ) / 2 ) = Z')], '( ( 1 / 2 ) - ( ( 2 x. Z ) / 2 ) ) = %s' % hz)],
                    '( ( 1 - ( 2 x. Z ) ) / 2 ) = %s' % hz)])
    Mh, Ph = '( M ^c %s )' % hz, '( _pi ^c %s )' % hz
    phc = D(w, A, 'cxpcld', [cl.mem('_pi', 'CC'), hzc], '%s e. CC' % Ph); phn = D(w, A, 'cxpne0d', [cl.mem('_pi', 'CC'), cl.ne0('_pi'), hzc], '%s =/= 0' % Ph)
    mhc = D(w, A, 'cxpcld', [cl.mem('M', 'CC'), hzc], '%s e. CC' % Mh)
    pw = chain(w, A, ['( %s x. %s )' % (Y2, X), '( %s x. ( 1 / %s ) )' % (Y2, Y1), '( %s / %s )' % (Y2, Y1), '( %s ^c ( %s - %s ) )' % (MPI, W2, W_), '( %s ^c %s )' % (MPI, hz),
                      '( %s / %s )' % (Mh, Ph), '( %s x. ( 1 / %s ) )' % (Mh, Ph), '( %s x. %s )' % (Mh, PiH)],
                 [D(w, A, 'oveq2d', [rp_], '( %s x. %s ) = ( %s x. ( 1 / %s ) )' % (Y2, X, Y2, Y1)),
                  ('r', D(w, A, 'divrecd', [y2c, y1c, y1n], '( %s / %s ) = ( %s x. ( 1 / %s ) )' % (Y2, Y1, Y2, Y1))),
                  ('r', D(w, A, 'cxpsubd', [mpc, mpn, w2c, wc], '( %s ^c ( %s - %s ) ) = ( %s / %s )' % (MPI, W2, W_, Y2, Y1))),
                  D(w, A, 'oveq2d', [zdif], '( %s ^c ( %s - %s ) ) = ( %s ^c %s )' % (MPI, W2, W_, MPI, hz)),
                  D(w, A, 'divcxpd', [cl.mem('M', 'RR'), cl.ge0('M'), cl.mem('_pi', 'RR+'), hzc], '( %s ^c %s ) = ( %s / %s )' % (MPI, hz, Mh, Ph)),
                  D(w, A, 'divrecd', [mhc, phc, phn], '( %s / %s ) = ( %s x. ( 1 / %s ) )' % (Mh, Ph, Mh, Ph)),
                  D(w, A, 'oveq2d', [D(w, A, 'eqtr3d', [D(w, A, 'oveq2d', [D(w, A, 'negsubdi2d', [cst(w, A, 'halfcn', '( 1 / 2 ) e. CC'), zc], '-u %s = ( Z - ( 1 / 2 ) )' % hz)],
                                                          '( _pi ^c -u %s ) = %s' % (hz, PiH)),
                                                        D(w, A, 'cxpnegd', [cl.mem('_pi', 'CC'), cl.ne0('_pi'), hzc], '( _pi ^c -u %s ) = ( 1 / %s )' % (hz, Ph))],
                                      '%s = ( 1 / %s )' % (PiH, Ph)) if False else
                                    D(w, A, 'eqtr3d', [D(w, A, 'cxpnegd', [cl.mem('_pi', 'CC'), cl.ne0('_pi'), hzc], '( _pi ^c -u %s ) = ( 1 / %s )' % (hz, Ph)),
                                                       D(w, A, 'oveq2d', [D(w, A, 'negsubdi2d', [cst(w, A, 'halfcn', '( 1 / 2 ) e. CC'), zc], '-u %s = ( Z - ( 1 / 2 ) )' % hz)],
                                                         '( _pi ^c -u %s ) = %s' % (hz, PiH))], '( 1 / %s ) = %s' % (Ph, PiH))],
                    '( %s x. ( 1 / %s ) ) = ( %s x. %s )' % (Mh, Ph, Mh, PiH))])
    # Gamma values
    G1dm = D(w, A, 'syl2anc', [D(w, A, 'addcld', [wc, one], '( %s + 1 ) e. CC' % W_),
                               D(w, A, 'breqtrrd', [linarith(w, A, [zr, p0], '0 < ( ( ( ( Re ` Z ) + P ) / 2 ) + 1 )', closure=cl),
                                                    D(w, A, 'eqtrd', [D(w, A, 'readdd', [wc, one], '( Re ` ( %s + 1 ) ) = ( ( Re ` %s ) + ( Re ` 1 ) )' % (W_, W_)),
                                                                      D(w, A, 'oveq12d', [reW, cst(w, A, 're1', '( Re ` 1 ) = 1')], '( ( Re ` %s ) + ( Re ` 1 ) ) = ( ( ( ( Re ` Z ) + P ) / 2 ) + 1 )' % W_)],
                                                      '( Re ` ( %s + 1 ) ) = ( ( ( ( Re ` Z ) + P ) / 2 ) + 1 )' % W_)], '0 < ( Re ` ( %s + 1 ) )' % W_), w.inst('zrenn')],
                  '( %s + 1 ) e. ( CC \\ ( ZZ \\ NN ) )' % W_)
    g1c = D(w, A, 'syl', [G1dm, w.inst('gamcl')], '%s e. CC' % G1); g1n = D(w, A, 'syl', [G1dm, w.inst('gamne0')], '%s =/= 0' % G1)
    spc2, reW2_, _ = reim_w(w, A, '( 1 - Z )', omz, pc, pr)
    re1z = D(w, A, 'eqtrd', [D(w, A, 'resubd', [one, zc], '( Re ` ( 1 - Z ) ) = ( ( Re ` 1 ) - ( Re ` Z ) )'), D(w, A, 'oveq1d', [cst(w, A, 're1', '( Re ` 1 ) = 1')], '( ( Re ` 1 ) - ( Re ` Z ) ) = ( 1 - ( Re ` Z ) )')],
             '( Re ` ( 1 - Z ) ) = ( 1 - ( Re ` Z ) )')
    rw2 = D(w, A, 'eqtrd', [reW2_, D(w, A, 'oveq1d', [D(w, A, 'oveq1d', [re1z], '( ( Re ` ( 1 - Z ) ) + P ) = ( ( 1 - ( Re ` Z ) ) + P )')], '( ( ( Re ` ( 1 - Z ) ) + P ) / 2 ) = ( ( ( 1 - ( Re ` Z ) ) + P ) / 2 )')],
            '( Re ` %s ) = ( ( ( 1 - ( Re ` Z ) ) + P ) / 2 )' % W2)
    G2dm = D(w, A, 'syl2anc', [w2c, D(w, A, 'breqtrrd', [linarith(w, A, [zr1, p0], '0 < ( ( ( 1 - ( Re ` Z ) ) + P ) / 2 )', closure=cl), rw2], '0 < ( Re ` %s )' % W2), w.inst('zrenn')],
             '%s e. ( CC \\ ( ZZ \\ NN ) )' % W2)
    g2c = D(w, A, 'syl', [G2dm, w.inst('gamcl')], '%s e. CC' % Ga2)
    Xc = D(w, A, 'cxpcld', [cl.mem(PM, 'CC'), wc], '%s e. CC' % X)
    wg = '( %s / %s )' % (W_, G1)
    wgc = D(w, A, 'divcld', [wc, g1c, g1n], '%s e. CC' % wg)
    LHS = '( %s x. %s )' % (LE.GAMFG('( 1 - Z )', 'P'), LE.GV('Z'))
    assert LE.GAMFG('( 1 - Z )', 'P') == '( %s x. %s )' % (Y2, Ga2)
    assert LE.GV('Z') == '( %s x. ( %s / %s ) )' % (W_, X, G1)
    e = chain(w, A, [LHS, '( ( %s x. %s ) x. ( %s x. %s ) )' % (Y2, Ga2, X, wg), '( ( %s x. %s ) x. ( %s x. %s ) )' % (Y2, X, Ga2, wg),
                     '( ( %s x. %s ) x. ( %s x. %s ) )' % (Mh, PiH, Ga2, wg), '( %s x. %s )' % (Mh, RQ), '( %s x. ( %s ` Z ) )' % (Mh, LE.QQ('P'))],
              [D(w, A, 'oveq2d', [D(w, A, 'eqtr3d', [D(w, A, 'divassd', [wc, Xc, g1c, g1n], '( ( %s x. %s ) / %s ) = %s' % (W_, X, G1, LE.GV('Z'))),
                                                     D(w, A, 'eqtrd', [D(w, A, 'oveq1d', [D(w, A, 'mulcomd', [wc, Xc], '( %s x. %s ) = ( %s x. %s )' % (W_, X, X, W_))], '( ( %s x. %s ) / %s ) = ( ( %s x. %s ) / %s )' % (W_, X, G1, X, W_, G1)),
                                                                       D(w, A, 'divassd', [Xc, wc, g1c, g1n], '( ( %s x. %s ) / %s ) = ( %s x. %s )' % (X, W_, G1, X, wg))],
                                                       '( ( %s x. %s ) / %s ) = ( %s x. %s )' % (W_, X, G1, X, wg))], '%s = ( %s x. %s )' % (LE.GV('Z'), X, wg))],
                 '%s = ( ( %s x. %s ) x. ( %s x. %s ) )' % (LHS, Y2, Ga2, X, wg)),
               D(w, A, 'mul4d', [y2c, g2c, Xc, wgc], '( ( %s x. %s ) x. ( %s x. %s ) ) = ( ( %s x. %s ) x. ( %s x. %s ) )' % (Y2, Ga2, X, wg, Y2, X, Ga2, wg)),
               D(w, A, 'oveq1d', [pw], '( ( %s x. %s ) x. ( %s x. %s ) ) = ( ( %s x. %s ) x. ( %s x. %s ) )' % (Y2, X, Ga2, wg, Mh, PiH, Ga2, wg)),
               D(w, A, 'mulassd', [mhc, D(w, A, 'cxpcld', [cl.mem('_pi', 'CC'), D(w, A, 'subcld', [zc, cst(w, A, 'halfcn', '( 1 / 2 ) e. CC')], '( Z - ( 1 / 2 ) ) e. CC')], '%s e. CC' % PiH),
                                   D(w, A, 'mulcld', [g2c, wgc], '( %s x. %s ) e. CC' % (Ga2, wg))], '( ( %s x. %s ) x. ( %s x. %s ) ) = ( %s x. %s )' % (Mh, PiH, Ga2, wg, Mh, RQ)),
               D(w, A, 'oveq2d', [D(w, A, 'eqcomd', [qv2], '%s = ( %s ` Z )' % (RQ, LE.QQ('P')))], '( %s x. %s ) = ( %s x. ( %s ` Z ) )' % (Mh, RQ, Mh, LE.QQ('P')))])
    w.qed([e], 'idi', SE['zl3gfr'])
    goe(w)


# ---------------------------------------------------------------- zl3fal
if wante('zl3fal', MAIN):
    w = W('zl3fal', 'Field algebra of the pole terms: with ` R e. { 0 , 1 } ` and, when ` R = 1 ` , ` G = ( Z / 2 ) H ` and ` B = 1 ` , the closed form plus ` R / ( Z - 1 ) ` is ` ( L - R ( 1 / Z + 1 / ( 1 - Z ) ) ) G ` .')
    A, Cc = ante_e('zl3fal')
    LHS = '( ( ( ( L x. G ) - ( R x. ( H / 2 ) ) ) + ( R x. ( ( G - B ) / ( Z - 1 ) ) ) ) + ( R / ( Z - 1 ) ) )'
    RHS = '( ( L - ( R x. ( ( 1 / Z ) + ( 1 / ( 1 - Z ) ) ) ) ) x. G )'
    assert Cc in ('%s = %s' % (LHS, RHS), '( %s = %s )' % (LHS, RHS)), Cc
    Cc = '%s = %s' % (LHS, RHS)
    cc = lambda v, st: (v, st)
    lc = D(w, A, 'simp1d' if False else 'simplll' if False else 'idi', [], '') if False else None
    h1 = D(w, A, 'simp1', [], '( ( L e. CC /\\ H e. CC ) /\\ ( G e. CC /\\ B e. CC ) )')
    lc = D(w, A, 'simpld', [D(w, A, 'simpld', [h1], '( L e. CC /\\ H e. CC )')], 'L e. CC'); hc = D(w, A, 'simprd', [D(w, A, 'simpld', [h1], '( L e. CC /\\ H e. CC )')], 'H e. CC')
    gc = D(w, A, 'simpld', [D(w, A, 'simprd', [h1], '( G e. CC /\\ B e. CC )')], 'G e. CC'); bc = D(w, A, 'simprd', [D(w, A, 'simprd', [h1], '( G e. CC /\\ B e. CC )')], 'B e. CC')
    h2 = D(w, A, 'simp2', [], '( Z e. CC /\\ Z =/= 0 /\\ Z =/= 1 )')
    zc = D(w, A, 'simp1d', [h2], 'Z e. CC'); z0 = D(w, A, 'simp2d', [h2], 'Z =/= 0'); z1 = D(w, A, 'simp3d', [h2], 'Z =/= 1')
    h3 = D(w, A, 'simp3', [], '( R e. { 0 , 1 } /\\ ( R = 1 -> ( G = ( ( Z / 2 ) x. H ) /\\ B = 1 ) ) )')
    rp = D(w, A, 'simpld', [h3], 'R e. { 0 , 1 }'); rimp = D(w, A, 'simprd', [h3], '( R = 1 -> ( G = ( ( Z / 2 ) x. H ) /\\ B = 1 ) )')
    one = cst(w, A, 'ax-1cn', '1 e. CC')
    zm1 = '( Z - 1 )'
    zm1c = D(w, A, 'subcld', [zc, one], '%s e. CC' % zm1)
    zm1n = D(w, A, 'subne0d', [zc, one, z1], '%s =/= 0' % zm1)
    omz = '( 1 - Z )'
    omzc = D(w, A, 'subcld', [one, zc], '%s e. CC' % omz)
    omzn = D(w, A, 'subne0d', [one, zc, D(w, A, 'necomd', [z1], '1 =/= Z')], '%s =/= 0' % omz)
    A0 = '( %s /\\ R = 0 )' % A; A1 = '( %s /\\ R = 1 )' % A
    L0 = lambda st, f: ad(w, A0, st, f); L1 = lambda st, f: ad(w, A1, st, f)
    # R = 0
    r0 = w.s([], 'simpr', '( %s -> R = 0 )' % A0)
    le0, nl = w.rewrite(LHS, {'R': ('0', r0)}, A0)
    re0, nr = w.rewrite(RHS, {'R': ('0', r0)}, A0)
    S = '( ( 1 / Z ) + ( 1 / %s ) )' % omz
    lg = '( L x. G )'
    lgc0 = L0(D(w, A, 'mulcld', [lc, gc], '%s e. CC' % lg), '%s e. CC' % lg)
    zz = lambda X, xc: D(w, A0, 'mul02d', [xc], '( 0 x. %s ) = 0' % X)
    hh = '( H / 2 )'; hhc = D(w, A, 'halfcld', [hc], '%s e. CC' % hh)
    dq = '( ( G - B ) / %s )' % zm1
    dqc = D(w, A, 'divcld', [D(w, A, 'subcld', [gc, bc], '( G - B ) e. CC'), zm1c, zm1n], '%s e. CC' % dq)
    sc_ = D(w, A, 'addcld', [D(w, A, 'reccld', [zc, z0], '( 1 / Z ) e. CC'), D(w, A, 'reccld', [omzc, omzn], '( 1 / %s ) e. CC' % omz)], '%s e. CC' % S)
    assert nl == '( ( ( %s - ( 0 x. %s ) ) + ( 0 x. %s ) ) + ( 0 / %s ) )' % (lg, hh, dq, zm1), nl
    l0 = chain(w, A0, [nl, '( ( ( %s - 0 ) + 0 ) + 0 )' % lg, lg],
               [D(w, A0, 'oveq12d', [D(w, A0, 'oveq12d', [D(w, A0, 'oveq2d', [zz(hh, L0(hhc, '%s e. CC' % hh))], '( %s - ( 0 x. %s ) ) = ( %s - 0 )' % (lg, hh, lg)), zz(dq, L0(dqc, '%s e. CC' % dq))],
                                                '( ( %s - ( 0 x. %s ) ) + ( 0 x. %s ) ) = ( ( %s - 0 ) + 0 )' % (lg, hh, dq, lg)),
                                      D(w, A0, 'div0d', [L0(zm1c, '%s e. CC' % zm1), L0(zm1n, '%s =/= 0' % zm1)], '( 0 / %s ) = 0' % zm1)], '%s = ( ( ( %s - 0 ) + 0 ) + 0 )' % (nl, lg)),
                chain(w, A0, ['( ( ( %s - 0 ) + 0 ) + 0 )' % lg, '( ( %s - 0 ) + 0 )' % lg, '( %s - 0 )' % lg, lg],
                      [D(w, A0, 'addridd', [D(w, A0, 'addcld', [D(w, A0, 'subcld', [lgc0, cst(w, A0, '0cn', '0 e. CC')], '( %s - 0 ) e. CC' % lg), cst(w, A0, '0cn', '0 e. CC')], '( ( %s - 0 ) + 0 ) e. CC' % lg)],
                         '( ( ( %s - 0 ) + 0 ) + 0 ) = ( ( %s - 0 ) + 0 )' % (lg, lg)),
                       D(w, A0, 'addridd', [D(w, A0, 'subcld', [lgc0, cst(w, A0, '0cn', '0 e. CC')], '( %s - 0 ) e. CC' % lg)], '( ( %s - 0 ) + 0 ) = ( %s - 0 )' % (lg, lg)),
                       D(w, A0, 'subid1d', [lgc0], '( %s - 0 ) = %s' % (lg, lg))])])
    assert nr == '( ( L - ( 0 x. %s ) ) x. G )' % S, nr
    r0e = chain(w, A0, [nr, '( ( L - 0 ) x. G )', lg],
                [D(w, A0, 'oveq1d', [D(w, A0, 'oveq2d', [zz(S, L0(sc_, '%s e. CC' % S))], '( L - ( 0 x. %s ) ) = ( L - 0 )' % S)], '%s = ( ( L - 0 ) x. G )' % nr),
                 D(w, A0, 'oveq1d', [D(w, A0, 'subid1d', [L0(lc, 'L e. CC')], '( L - 0 ) = L')], '( ( L - 0 ) x. G ) = %s' % lg)])
    case0 = D(w, A0, 'eqtr4d', [D(w, A0, 'eqtrd', [le0, l0], '%s = %s' % (LHS, lg)), D(w, A0, 'eqtrd', [re0, r0e], '%s = %s' % (RHS, lg))], Cc)
    # R = 1
    r1 = w.s([], 'simpr', '( %s -> R = 1 )' % A1)
    gb = D(w, A1, 'mpd', [r1, L1(rimp, '( R = 1 -> ( G = ( ( Z / 2 ) x. H ) /\\ B = 1 ) )')], '( G = ( ( Z / 2 ) x. H ) /\\ B = 1 )')
    ge = D(w, A1, 'simpld', [gb], 'G = ( ( Z / 2 ) x. H )'); be = D(w, A1, 'simprd', [gb], 'B = 1')
    le1, nl1 = w.rewrite(LHS, {'R': ('1', r1), 'B': ('1', be)}, A1)
    re1, nr1 = w.rewrite(RHS, {'R': ('1', r1)}, A1)
    gc1, lc1, hc1, zc1 = L1(gc, 'G e. CC'), L1(lc, 'L e. CC'), L1(hc, 'H e. CC'), L1(zc, 'Z e. CC')
    zm1c1, zm1n1 = L1(zm1c, '%s e. CC' % zm1), L1(zm1n, '%s =/= 0' % zm1)
    one1 = cst(w, A1, 'ax-1cn', '1 e. CC')
    T = '( %s - %s )' % (lg, hh)
    Tc = D(w, A1, 'subcld', [D(w, A1, 'mulcld', [lc1, gc1], '%s e. CC' % lg), L1(hhc, '%s e. CC' % hh)], '%s e. CC' % T)
    gz = '( G / %s )' % zm1
    gm1 = '( ( G - 1 ) / %s )' % zm1
    gm1c = D(w, A1, 'divcld', [D(w, A1, 'subcld', [gc1, one1], '( G - 1 ) e. CC'), zm1c1, zm1n1], '%s e. CC' % gm1)
    oz = '( 1 / %s )' % zm1
    ozc = D(w, A1, 'divcld', [one1, zm1c1, zm1n1], '%s e. CC' % oz)
    assert nl1 == '( ( ( %s - ( 1 x. %s ) ) + ( 1 x. %s ) ) + ( 1 / %s ) )' % (lg, hh, gm1, zm1), nl1
    l1 = chain(w, A1, [nl1, '( ( %s + %s ) + %s )' % (T, gm1, oz), '( %s + ( %s + %s ) )' % (T, gm1, oz), '( %s + ( ( ( G - 1 ) + 1 ) / %s ) )' % (T, zm1), '( %s + %s )' % (T, gz)],
               [D(w, A1, 'oveq1d', [D(w, A1, 'oveq12d', [D(w, A1, 'oveq2d', [D(w, A1, 'mullidd', [L1(hhc, '%s e. CC' % hh)], '( 1 x. %s ) = %s' % (hh, hh))], '( %s - ( 1 x. %s ) ) = %s' % (lg, hh, T)),
                                                         D(w, A1, 'mullidd', [gm1c], '( 1 x. %s ) = %s' % (gm1, gm1))], '( ( %s - ( 1 x. %s ) ) + ( 1 x. %s ) ) = ( %s + %s )' % (lg, hh, gm1, T, gm1))],
                  '%s = ( ( %s + %s ) + %s )' % (nl1, T, gm1, oz)),
                D(w, A1, 'addassd', [Tc, gm1c, ozc], '( ( %s + %s ) + %s ) = ( %s + ( %s + %s ) )' % (T, gm1, oz, T, gm1, oz)),
                D(w, A1, 'oveq2d', [D(w, A1, 'eqcomd', [D(w, A1, 'divdird', [D(w, A1, 'subcld', [gc1, one1], '( G - 1 ) e. CC'), one1, zm1c1, zm1n1], '( ( ( G - 1 ) + 1 ) / %s ) = ( %s + %s )' % (zm1, gm1, oz))],
                                                      '( %s + %s ) = ( ( ( G - 1 ) + 1 ) / %s )' % (gm1, oz, zm1))], '( %s + ( %s + %s ) ) = ( %s + ( ( ( G - 1 ) + 1 ) / %s ) )' % (T, gm1, oz, T, zm1)),
                D(w, A1, 'oveq2d', [D(w, A1, 'oveq1d', [D(w, A1, 'npcand', [gc1, one1], '( ( G - 1 ) + 1 ) = G')], '( ( ( G - 1 ) + 1 ) / %s ) = %s' % (zm1, gz))],
                  '( %s + ( ( ( G - 1 ) + 1 ) / %s ) ) = ( %s + %s )' % (T, zm1, T, gz))])
    assert nr1 == '( ( L - ( 1 x. %s ) ) x. G )' % S, nr1
    omzc1, omzn1, z01 = L1(omzc, '%s e. CC' % omz), L1(omzn, '%s =/= 0' % omz), L1(z0, 'Z =/= 0')
    gZ, g1z = '( G / Z )', '( G / %s )' % omz
    negz = D(w, A1, 'negsubdi2d', [zc1, one1], '-u %s = %s' % (zm1, omz))
    g1ze = D(w, A1, 'eqtrd', [D(w, A1, 'divneg2d', [gc1, zm1c1, zm1n1], '-u %s = ( G / -u %s )' % (gz, zm1)), D(w, A1, 'oveq2d', [negz], '( G / -u %s ) = %s' % (zm1, g1z))], '-u %s = %s' % (gz, g1z))
    gZe = chain(w, A1, [gZ, '( ( ( Z / 2 ) x. H ) / Z )', '( ( ( Z x. H ) / 2 ) / Z )', '( ( Z x. %s ) / Z )' % hh, hh],
                [D(w, A1, 'oveq1d', [ge], '%s = ( ( ( Z / 2 ) x. H ) / Z )' % gZ),
                 D(w, A1, 'oveq1d', [D(w, A1, 'eqcomd', [D(w, A1, 'div32d' if False else 'div23d', [zc1, hc1, cst(w, A1, '2cn', '2 e. CC'), cst(w, A1, '2ne0', '2 =/= 0')], '( ( Z x. H ) / 2 ) = ( ( Z / 2 ) x. H )')],
                                                       '( ( Z / 2 ) x. H ) = ( ( Z x. H ) / 2 )')], '( ( ( Z / 2 ) x. H ) / Z ) = ( ( ( Z x. H ) / 2 ) / Z )'),
                 D(w, A1, 'oveq1d', [D(w, A1, 'divassd', [zc1, hc1, cst(w, A1, '2cn', '2 e. CC'), cst(w, A1, '2ne0', '2 =/= 0')], '( ( Z x. H ) / 2 ) = ( Z x. %s )' % hh)],
                   '( ( ( Z x. H ) / 2 ) / Z ) = ( ( Z x. %s ) / Z )' % hh),
                 D(w, A1, 'divcan3d', [L1(hhc, '%s e. CC' % hh), zc1, z01], '( ( Z x. %s ) / Z ) = %s' % (hh, hh))])
    r1e = chain(w, A1, [nr1, '( ( L - %s ) x. G )' % S, '( %s - ( %s x. G ) )' % (lg, S), '( %s - ( ( ( 1 / Z ) x. G ) + ( ( 1 / %s ) x. G ) ) )' % (lg, omz),
                        '( %s - ( %s + %s ) )' % (lg, gZ, g1z), '( %s - ( %s + -u %s ) )' % (lg, hh, gz), '( %s - ( %s - %s ) )' % (lg, hh, gz), '( %s + %s )' % (T, gz)],
                [D(w, A1, 'oveq1d', [D(w, A1, 'oveq2d', [D(w, A1, 'mullidd', [L1(sc_, '%s e. CC' % S)], '( 1 x. %s ) = %s' % (S, S))], '( L - ( 1 x. %s ) ) = ( L - %s )' % (S, S))],
                   '%s = ( ( L - %s ) x. G )' % (nr1, S)),
                 D(w, A1, 'subdird', [lc1, L1(sc_, '%s e. CC' % S), gc1], '( ( L - %s ) x. G ) = ( %s - ( %s x. G ) )' % (S, lg, S)),
                 D(w, A1, 'oveq2d', [D(w, A1, 'adddird', [D(w, A1, 'reccld', [zc1, z01], '( 1 / Z ) e. CC'), D(w, A1, 'reccld', [omzc1, omzn1], '( 1 / %s ) e. CC' % omz), gc1],
                                       '( %s x. G ) = ( ( ( 1 / Z ) x. G ) + ( ( 1 / %s ) x. G ) )' % (S, omz))],
                   '( %s - ( %s x. G ) ) = ( %s - ( ( ( 1 / Z ) x. G ) + ( ( 1 / %s ) x. G ) ) )' % (lg, S, lg, omz)),
                 D(w, A1, 'oveq2d', [D(w, A1, 'oveq12d', [D(w, A1, 'eqcomd', [D(w, A1, 'divrec2d', [gc1, zc1, z01], '%s = ( ( 1 / Z ) x. G )' % gZ)], '( ( 1 / Z ) x. G ) = %s' % gZ),
                                                         D(w, A1, 'eqcomd', [D(w, A1, 'divrec2d', [gc1, omzc1, omzn1], '%s = ( ( 1 / %s ) x. G )' % (g1z, omz))], '( ( 1 / %s ) x. G ) = %s' % (omz, g1z))],
                                       '( ( ( 1 / Z ) x. G ) + ( ( 1 / %s ) x. G ) ) = ( %s + %s )' % (omz, gZ, g1z))],
                   '( %s - ( ( ( 1 / Z ) x. G ) + ( ( 1 / %s ) x. G ) ) ) = ( %s - ( %s + %s ) )' % (lg, omz, lg, gZ, g1z)),
                 D(w, A1, 'oveq2d', [D(w, A1, 'oveq12d', [gZe, D(w, A1, 'eqcomd', [g1ze], '%s = -u %s' % (g1z, gz))], '( %s + %s ) = ( %s + -u %s )' % (gZ, g1z, hh, gz))],
                   '( %s - ( %s + %s ) ) = ( %s - ( %s + -u %s ) )' % (lg, gZ, g1z, lg, hh, gz)),
                 D(w, A1, 'oveq2d', [D(w, A1, 'negsubd', [L1(hhc, '%s e. CC' % hh), D(w, A1, 'divcld', [gc1, zm1c1, zm1n1], '%s e. CC' % gz)], '( %s + -u %s ) = ( %s - %s )' % (hh, gz, hh, gz))],
                   '( %s - ( %s + -u %s ) ) = ( %s - ( %s - %s ) )' % (lg, hh, gz, lg, hh, gz)),
                 D(w, A1, 'subsubd', [D(w, A1, 'mulcld', [lc1, gc1], '%s e. CC' % lg), L1(hhc, '%s e. CC' % hh), D(w, A1, 'divcld', [gc1, zm1c1, zm1n1], '%s e. CC' % gz)],
                   '( %s - ( %s - %s ) ) = ( %s + %s )' % (lg, hh, gz, T, gz))])
    case1 = D(w, A1, 'eqtr4d', [D(w, A1, 'eqtrd', [le1, l1], '%s = ( %s + %s )' % (LHS, T, gz)), D(w, A1, 'eqtrd', [re1, r1e], '%s = ( %s + %s )' % (RHS, T, gz))], Cc)
    fin = w.s([case0, case1, w.s([rp, w.inst('elpri')], 'syl', '( %s -> ( R = 0 \\/ R = 1 ) )' % A)], 'mpjaodan', '( %s -> %s )' % (A, Cc))
    w.qed([fin], 'idi', SE['zl3fal'])
    goe(w)


# ---------------------------------------------------------------- zl3rem
if wante('zl3rem', MAIN):
    w = W('zl3rem', 'Removable singularity: for ` G ` holomorphic on ` D ` with ` G ( P ) = 0 ` at an interior point of a rectangle in ` D ` , the difference quotient extended by ` G \' ( P ) ` is holomorphic ( ~ zl3qvp with the bounds of ~ crectrbd , ~ crectbnd ).')
    A, Cc = ante_e('zl3rem')
    FR = "( ( ( A cseg ( ( Re ` B ) + ( _i x. ( Im ` A ) ) ) ) u. ( ( ( Re ` B ) + ( _i x. ( Im ` A ) ) ) cseg B ) ) u. ( ( B cseg ( ( Re ` A ) + ( _i x. ( Im ` B ) ) ) ) u. ( ( ( Re ` A ) + ( _i x. ( Im ` B ) ) ) cseg A ) ) )"
    INS = '( P e. CC /\\ ( ( ( Re ` A ) < ( Re ` P ) /\\ ( Re ` P ) < ( Re ` B ) ) /\\ ( ( Im ` A ) < ( Im ` P ) /\\ ( Im ` P ) < ( Im ` B ) ) ) )'
    RC = lambda r: '( ( %s <_ ( ( Re ` P ) - ( Re ` A ) ) /\\ %s <_ ( ( Re ` B ) - ( Re ` P ) ) ) /\\ ( %s <_ ( ( Im ` P ) - ( Im ` A ) ) /\\ %s <_ ( ( Im ` B ) - ( Im ` P ) ) ) )' % (r, r, r, r)
    BN = lambda m, X: 'A. u e. %s ( abs ` ( G ` u ) ) <_ %s' % (X, m)
    hol = D(w, A, 'simp1', [], HOL('G', 'D'))
    rect = D(w, A, 'simp2', [], LE.RECT)
    g0 = D(w, A, 'simp3', [], '( G ` P ) = 0')
    abP = D(w, A, 'simpld', [rect], '( ( A e. CC /\\ B e. CC ) /\\ %s )' % INS)
    ab = D(w, A, 'simpld', [abP], '( A e. CC /\\ B e. CC )'); ins = D(w, A, 'simprd', [abP], INS)
    ss = D(w, A, 'simprd', [rect], '( A crect B ) C_ D')
    gcn = D(w, A, 'simpld', [hol], 'G e. ( D -cn-> CC )')
    exr = D(w, A, 'syl', [abP, w.inst('crectrbd')], 'E. r e. RR+ %s' % RC('r'))
    exm0 = D(w, A, 'syl2anc', [ab, D(w, A, 'jca', [gcn, ss], '( G e. ( D -cn-> CC ) /\\ ( A crect B ) C_ D )'), w.inst('crectbnd')], 'E. m e. RR %s' % BN('m', '( A crect B )'))
    BNv = lambda m, X: 'A. v e. %s ( abs ` ( G ` v ) ) <_ %s' % (X, m)
    bodyuv = lambda q: '( abs ` ( G ` %s ) ) <_ m' % q
    cbuv = w.s([wsub(w, bodyuv, 'u', 'v')], 'cbvralvw', '( %s <-> %s )' % (BN('m', '( A crect B )'), BNv('m', '( A crect B )')))
    exm = D(w, A, 'mpbid', [exm0, w.s([w.s([cbuv], 'rexbii', '( E. m e. RR %s <-> E. m e. RR %s )' % (BN('m', '( A crect B )'), BNv('m', '( A crect B )')))], 'a1i',
                                      '( %s -> ( E. m e. RR %s <-> E. m e. RR %s ) )' % (A, BN('m', '( A crect B )'), BNv('m', '( A crect B )')))], 'E. m e. RR %s' % BNv('m', '( A crect B )'))
    A2 = '( ( %s /\\ ( r e. RR+ /\\ %s ) ) /\\ ( m e. RR /\\ %s ) )' % (A, RC('r'), BNv('m', '( A crect B )'))
    L2 = lambda st, f: ad(w, A2, ad(w, '( %s /\\ ( r e. RR+ /\\ %s ) )' % (A, RC('r')), st, f), f)
    rrp = D(w, A2, 'simplrl', [], 'r e. RR+'); rc = D(w, A2, 'simplrr', [], RC('r'))
    mr = D(w, A2, 'simprl', [], 'm e. RR'); bm = D(w, A2, 'simprr', [], BNv('m', '( A crect B )'))
    ins2 = L2(ins, INS)
    ab2 = L2(ab, '( A e. CC /\\ B e. CC )')
    ltre = D(w, A2, 'lttrd', [D(w, A2, 'recld', [D(w, A2, 'simpld', [ab2], 'A e. CC')], '( Re ` A ) e. RR'), D(w, A2, 'recld', [D(w, A2, 'simpld', [ins2], 'P e. CC')], '( Re ` P ) e. RR'),
                               D(w, A2, 'recld', [D(w, A2, 'simprd', [ab2], 'B e. CC')], '( Re ` B ) e. RR'),
                               D(w, A2, 'simplld', [D(w, A2, 'simprd', [ins2], '( ( ( Re ` A ) < ( Re ` P ) /\\ ( Re ` P ) < ( Re ` B ) ) /\\ ( ( Im ` A ) < ( Im ` P ) /\\ ( Im ` P ) < ( Im ` B ) ) )')], '( Re ` A ) < ( Re ` P )') if False else
                               D(w, A2, 'simpld', [D(w, A2, 'simpld', [D(w, A2, 'simprd', [ins2], '( ( ( Re ` A ) < ( Re ` P ) /\\ ( Re ` P ) < ( Re ` B ) ) /\\ ( ( Im ` A ) < ( Im ` P ) /\\ ( Im ` P ) < ( Im ` B ) ) )')], '( ( Re ` A ) < ( Re ` P ) /\\ ( Re ` P ) < ( Re ` B ) )')], '( Re ` A ) < ( Re ` P )'),
                               D(w, A2, 'simprd', [D(w, A2, 'simpld', [D(w, A2, 'simprd', [ins2], '( ( ( Re ` A ) < ( Re ` P ) /\\ ( Re ` P ) < ( Re ` B ) ) /\\ ( ( Im ` A ) < ( Im ` P ) /\\ ( Im ` P ) < ( Im ` B ) ) )')], '( ( Re ` A ) < ( Re ` P ) /\\ ( Re ` P ) < ( Re ` B ) )')], '( Re ` P ) < ( Re ` B )')],
           '( Re ` A ) < ( Re ` B )')
    imb = D(w, A2, 'simprd', [D(w, A2, 'simprd', [ins2], '( ( ( Re ` A ) < ( Re ` P ) /\\ ( Re ` P ) < ( Re ` B ) ) /\\ ( ( Im ` A ) < ( Im ` P ) /\\ ( Im ` P ) < ( Im ` B ) ) )')], '( ( Im ` A ) < ( Im ` P ) /\\ ( Im ` P ) < ( Im ` B ) )')
    ltim = D(w, A2, 'lttrd', [D(w, A2, 'imcld', [D(w, A2, 'simpld', [ab2], 'A e. CC')], '( Im ` A ) e. RR'), D(w, A2, 'imcld', [D(w, A2, 'simpld', [ins2], 'P e. CC')], '( Im ` P ) e. RR'),
                               D(w, A2, 'imcld', [D(w, A2, 'simprd', [ab2], 'B e. CC')], '( Im ` B ) e. RR'), D(w, A2, 'simpld', [imb], '( Im ` A ) < ( Im ` P )'), D(w, A2, 'simprd', [imb], '( Im ` P ) < ( Im ` B )')],
           '( Im ` A ) < ( Im ` B )')
    fru = D(w, A2, 'syl2anc', [ab2, D(w, A2, 'jca', [D(w, A2, 'ltled', [D(w, A2, 'recld', [D(w, A2, 'simpld', [ab2], 'A e. CC')], '( Re ` A ) e. RR'), D(w, A2, 'recld', [D(w, A2, 'simprd', [ab2], 'B e. CC')], '( Re ` B ) e. RR'), ltre], '( Re ` A ) <_ ( Re ` B )'),
                                                    D(w, A2, 'ltled', [D(w, A2, 'imcld', [D(w, A2, 'simpld', [ab2], 'A e. CC')], '( Im ` A ) e. RR'), D(w, A2, 'imcld', [D(w, A2, 'simprd', [ab2], 'B e. CC')], '( Im ` B ) e. RR'), ltim], '( Im ` A ) <_ ( Im ` B )')],
                                        '( ( Re ` A ) <_ ( Re ` B ) /\\ ( Im ` A ) <_ ( Im ` B ) )'), w.inst('crectfru')], '%s C_ ( A crect B )' % FR)
    bfv = D(w, A2, 'mpd', [bm, D(w, A2, 'syl', [fru, w.inst('ssralv')], '( %s -> %s )' % (BNv('m', '( A crect B )'), BNv('m', FR)))], BNv('m', FR))
    bfr = D(w, A2, 'mpbid', [bfv, w.s([w.s([wsub(w, bodyuv, 'v', 'u')], 'cbvralvw', '( %s <-> %s )' % (BNv('m', FR), BN('m', FR)))], 'a1i', '( %s -> ( %s <-> %s ) )' % (A2, BNv('m', FR), BN('m', FR)))], BN('m', FR))
    Cx = '( j e. NN0 |-> ( ( y e. ( ( A crect B ) \\ { P } ) |-> ( ( G ` y ) / ( ( y - P ) ^ ( j + 1 ) ) ) ) rectint <. A , B >. ) )'
    QB = lambda v: 'if ( %s = P , ( ( %s ` 1 ) / ( 2 x. ( _i x. _pi ) ) ) , ( ( G ` %s ) / ( ( %s - P ) ^ 1 ) ) )' % (v, Cx, v, v)
    Qx = '( x e. D |-> %s )' % QB('x')
    qdef = w.s([vsub(w, QB, 'x', 'z')], 'cbvmptv', '%s = ( z e. D |-> %s )' % (Qx, QB('z')))
    HYP = '( ( ( %s /\\ ( ( A e. CC /\\ B e. CC ) /\\ %s /\\ ( A crect B ) C_ D ) ) /\\ ( ( ( r e. RR /\\ %s ) /\\ 0 < r ) /\\ ( m e. RR /\\ %s ) ) ) /\\ ( G ` P ) = 0 )' % (
        HOL('G', 'D'), INS, RC('r'), BN('m', FR))
    hyp_ = D(w, A2, 'jca', [D(w, A2, 'jca', [D(w, A2, 'jca', [L2(hol, HOL('G', 'D')), D(w, A2, '3jca', [ab2, ins2, L2(ss, '( A crect B ) C_ D')], '( ( A e. CC /\\ B e. CC ) /\\ %s /\\ ( A crect B ) C_ D )' % INS)],
                                                       '( %s /\\ ( ( A e. CC /\\ B e. CC ) /\\ %s /\\ ( A crect B ) C_ D ) )' % (HOL('G', 'D'), INS)),
                                                 D(w, A2, 'jca', [D(w, A2, 'jca', [D(w, A2, 'jca', [D(w, A2, 'rpred', [rrp], 'r e. RR'), rc], '( r e. RR /\\ %s )' % RC('r')), D(w, A2, 'rpgt0d', [rrp], '0 < r')],
                                                                                   '( ( r e. RR /\\ %s ) /\\ 0 < r )' % RC('r')), D(w, A2, 'jca', [mr, bfr], '( m e. RR /\\ %s )' % BN('m', FR))],
                                                   '( ( ( r e. RR /\\ %s ) /\\ 0 < r ) /\\ ( m e. RR /\\ %s ) )' % (RC('r'), BN('m', FR)))],
                                   HYP[2:HYP.rindex(' /\\ ( G ` P ) = 0 )')]),
                            L2(g0, '( G ` P ) = 0')], HYP)
    qvp = D(w, A2, 'syl', [hyp_, w.s([w.s([], 'eqid', '%s = %s' % (Cx, Cx)), qdef], 'zl3qvp', '( %s -> ( %s /\\ ( %s ` P ) = ( ( CC _D G ) ` P ) ) )' % (HYP, HOL(Qx, 'D'), Qx))],
            '( %s /\\ ( %s ` P ) = ( ( CC _D G ) ` P ) )' % (HOL(Qx, 'D'), Qx))
    holq = D(w, A2, 'simpld', [qvp], HOL(Qx, 'D')); qp = D(w, A2, 'simprd', [qvp], '( %s ` P ) = ( ( CC _D G ) ` P )' % Qx)
    pD = D(w, A2, 'sseldd', [L2(ss, '( A crect B ) C_ D'), D(w, A2, 'syl', [L2(abP, '( ( A e. CC /\\ B e. CC ) /\\ %s )' % INS), w.inst('crectinp')], 'P e. ( A crect B )')], 'P e. D')
    X1 = '( ( %s ` 1 ) / ( 2 x. ( _i x. _pi ) ) )' % Cx
    vx = ('ifex', [w.s([], 'ovex', '%s e. _V' % X1), w.s([], 'ovex', '( ( G ` P ) / ( ( P - P ) ^ 1 ) ) e. _V')])
    qvP = fv1(w, A2, 'x', 'D', QB, 'P', pD, vx)
    ifp = D(w, A2, 'iftrued', [D(w, A2, 'eqidd', [], 'P = P')], '%s = %s' % (QB('P'), X1))
    x1e = D(w, A2, 'eqtr3d', [D(w, A2, 'eqtrd', [qvP, ifp], '( %s ` P ) = %s' % (Qx, X1)), qp], '%s = ( ( CC _D G ) ` P )' % X1)
    Au = '( %s /\\ u e. D )' % A2
    ud = w.s([], 'simpr', '( %s -> u e. D )' % Au)
    dcc = D(w, A2, 'syl', [D(w, A2, 'simpld', [L2(hol, HOL('G', 'D'))], 'G e. ( D -cn-> CC )'), w.inst('cncfrss')], 'D C_ CC')
    uc = D(w, Au, 'sseldd', [ad(w, Au, dcc, 'D C_ CC'), ud], 'u e. CC')
    pc = D(w, Au, 'sseldd', [ad(w, Au, dcc, 'D C_ CC'), ad(w, Au, pD, 'P e. D')], 'P e. CC')
    QRb = 'if ( u = P , ( ( CC _D G ) ` P ) , ( ( G ` u ) / ( u - P ) ) )'
    br = D(w, Au, 'ifeq12d' if False else 'ifeq12d', [D(w, Au, 'eqcomd', [ad(w, Au, x1e, '%s = ( ( CC _D G ) ` P )' % X1)], '( ( CC _D G ) ` P ) = %s' % X1),
                                                     D(w, Au, 'oveq2d', [D(w, Au, 'eqcomd', [D(w, Au, 'exp1d', [D(w, Au, 'subcld', [uc, pc], '( u - P ) e. CC')], '( ( u - P ) ^ 1 ) = ( u - P )')], '( u - P ) = ( ( u - P ) ^ 1 )')],
                                                       '( ( G ` u ) / ( u - P ) ) = ( ( G ` u ) / ( ( u - P ) ^ 1 ) )')], '%s = %s' % (QRb, QB('u')))
    me = D(w, A2, 'mpteq2dva', [br], '%s = ( u e. D |-> %s )' % (LE.QR, QB('u')))
    cbu = w.s([vsub(w, QB, 'u', 'x')], 'cbvmptv', '( u e. D |-> %s ) = %s' % (QB('u'), Qx))
    eqq = D(w, A2, 'eqtrd', [me, w.s([cbu], 'a1i', '( %s -> ( u e. D |-> %s ) = %s )' % (A2, QB('u'), Qx))], '%s = %s' % (LE.QR, Qx))
    fin2 = D(w, A2, 'mpbird', [holq, hol_eq(w, A2, eqq, LE.QR, Qx, 'D')], HOL(LE.QR, 'D'))
    A1 = '( %s /\\ ( r e. RR+ /\\ %s ) )' % (A, RC('r'))
    s1 = w.s([w.s([fin2], 'anassrs', '( ( ( %s /\\ m e. RR ) /\\ %s ) -> %s )' % (A1, BNv('m', '( A crect B )'), HOL(LE.QR, 'D')))], 'ex',
             '( ( %s /\\ m e. RR ) -> ( %s -> %s ) )' % (A1, BNv('m', '( A crect B )'), HOL(LE.QR, 'D')))
    s2 = D(w, A1, 'rexlimdva', [s1], '( E. m e. RR %s -> %s )' % (BNv('m', '( A crect B )'), HOL(LE.QR, 'D')))
    s3 = D(w, A1, 'mpd', [ad(w, A1, exm, 'E. m e. RR %s' % BNv('m', '( A crect B )')), s2], HOL(LE.QR, 'D'))
    s4 = w.s([w.s([s3], 'anassrs', '( ( ( %s /\\ r e. RR+ ) /\\ %s ) -> %s )' % (A, RC('r'), HOL(LE.QR, 'D')))], 'ex', '( ( %s /\\ r e. RR+ ) -> ( %s -> %s ) )' % (A, RC('r'), HOL(LE.QR, 'D')))
    s5 = D(w, A, 'rexlimdva', [s4], '( E. r e. RR+ %s -> %s )' % (RC('r'), HOL(LE.QR, 'D')))
    w.qed([D(w, A, 'mpd', [exr, s5], HOL(LE.QR, 'D'))], 'idi', SE['zl3rem'])
    goe(w)


UO = LE.UO
STR = LE.STR


def uo_facts(w, A):
    opn = cst(w, A, 'z6mstopn', '%s e. ( TopOpen ` CCfld )' % UO)
    return opn


def uo_mem(w, Av, v, vin):
    """from ( Av -> v e. UO ): v e. CC, -1 < Re v, Re v < 3"""
    b = D(w, Av, 'mpbid', [vin, D(w, Av, 'syl2anc', [cst(w, Av, 'neg1rr', '-u 1 e. RR') and D(w, Av, 'rexrd', [cst(w, Av, 'neg1rr', '-u 1 e. RR')], '-u 1 e. RR*'),
                                                   D(w, Av, 'rexrd', [cst(w, Av, '3re', '3 e. RR')], '3 e. RR*'), w.inst('z6melst')],
                                   '( %s e. %s <-> ( %s e. CC /\\ ( -u 1 < ( Re ` %s ) /\\ ( Re ` %s ) < 3 ) ) )' % (v, UO, v, v, v))],
          '( %s e. CC /\\ ( -u 1 < ( Re ` %s ) /\\ ( Re ` %s ) < 3 ) )' % (v, v, v))
    return D(w, Av, 'simpld', [b], '%s e. CC' % v), D(w, Av, 'simpld', [D(w, Av, 'simprd', [b], '( -u 1 < ( Re ` %s ) /\\ ( Re ` %s ) < 3 )' % (v, v))], '-u 1 < ( Re ` %s )' % v), \
        D(w, Av, 'simprd', [D(w, Av, 'simprd', [b], '( -u 1 < ( Re ` %s ) /\\ ( Re ` %s ) < 3 )' % (v, v))], '( Re ` %s ) < 3' % v)


def aff_hol(w, A, a, b, ac, bc, Dm, opn, new='y'):
    """HOL ( ( new e. Dm |-> ( ( a x. new ) + b ) ) , Dm ) via zl3haff and a rebinding"""
    fz = lambda v: '( ( %s x. %s ) + %s )' % (a, v, b)
    h0 = D(w, A, 'syl2anc', [D(w, A, 'jca', [ac, bc], '( %s e. CC /\\ %s e. CC )' % (a, b)), opn, w.inst('zl3haff')], HOL('( z e. %s |-> %s )' % (Dm, fz('z')), Dm))
    return rebind(w, A, h0, fz, Dm, 'z', new)


def rebind(w, A, hst, fn, Dm, old, new):
    Fo, Fn = '( %s e. %s |-> %s )' % (old, Dm, fn(old)), '( %s e. %s |-> %s )' % (new, Dm, fn(new))
    cb = w.s([w.s([vsub(w, fn, old, new)], 'cbvmptv', '%s = %s' % (Fo, Fn))], 'a1i', '( %s -> %s = %s )' % (A, Fo, Fn))
    return D(w, A, 'mpbid', [hst, hol_eq(w, A, cb, Fo, Fn, Dm)], HOL(Fn, Dm))


def hol_exp(w, A):
    """( A -> HOL ( exp , CC ) )"""
    dm = w.s([w.s([w.s([w.s([], 'dvef', '( CC _D exp ) = exp')], 'dmeqi', 'dom ( CC _D exp ) = dom exp'), w.s([w.s([], 'eff', 'exp : CC --> CC')], 'fdmi', 'dom exp = CC')], 'eqtri', 'dom ( CC _D exp ) = CC')],
             'eqimss2i', 'CC C_ dom ( CC _D exp )')
    return D(w, A, 'jca', [cst(w, A, 'efcn', 'exp e. ( CC -cn-> CC )'), cst(w, A, 'idi', 'CC C_ dom ( CC _D exp )') if False else w.s([dm], 'a1i', '( %s -> CC C_ dom ( CC _D exp ) )' % A)], HOL('exp', 'CC'))


# ---------------------------------------------------------------- zl3ghl
if wante('zl3ghl', MAIN):
    w = W('zl3ghl', '` h ( x ) = ( pi / M ) ^ w / Gamma ( w + 1 ) ` and ` g ( x ) = w h ( x ) ` , ` w = ( x + P ) / 2 ` , are holomorphic on ` U = Re^-1 ( -1 , 3 ) ` ( ~ zl3hco , ~ z6gamhol , ~ holdiv , ~ holmul ).')
    A, Cc = ante_e('zl3ghl')
    mn = D(w, A, 'simpl', [], 'M e. NN'); pp = D(w, A, 'simpr', [], 'P e. { 0 , 1 }')
    pn, pr, p0, p1 = p01(w, A, pp)
    pc = D(w, A, 'recnd', [pr], 'P e. CC')
    cl, pmr, mpr = pm_facts(w, A, mn)
    opn = uo_facts(w, A)
    LG = '( log ` %s )' % PM
    lgc = D(w, A, 'recnd', [D(w, A, 'relogcld', [pmr], '%s e. RR' % LG)], '%s e. CC' % LG)
    a1, b1 = '( %s / 2 )' % LG, '( ( P / 2 ) x. %s )' % LG
    ph2 = D(w, A, 'halfcld', [pc], '( P / 2 ) e. CC')
    hE = aff_hol(w, A, a1, b1, D(w, A, 'halfcld', [lgc], '%s e. CC' % a1), D(w, A, 'mulcld', [ph2, lgc], '%s e. CC' % b1), UO, opn)
    AFE = '( y e. %s |-> ( ( %s x. y ) + %s ) )' % (UO, a1, b1)
    a2, b2 = '( 1 / 2 )', '( ( P / 2 ) + 1 )'
    hG = aff_hol(w, A, a2, b2, cst(w, A, 'halfcn', '( 1 / 2 ) e. CC'), D(w, A, 'addcld', [ph2, cst(w, A, 'ax-1cn', '1 e. CC')], '%s e. CC' % b2), UO, opn)
    AFG = '( y e. %s |-> ( ( %s x. y ) + %s ) )' % (UO, a2, b2)
    HP0 = "( `' Re \" ( 0 (,) +oo ) )"
    GAMz = lambda v: '( _G ` %s )' % v
    gam = rebind(w, A, cst(w, A, 'z6gamhol', HOL('( z e. %s |-> ( _G ` z ) )' % HP0, HP0)), GAMz, HP0, 'z', 'y')
    GAMy = '( y e. %s |-> ( _G ` y ) )' % HP0
    Av = '( %s /\\ v e. %s )' % (A, UO)
    vin = w.s([], 'simpr', '( %s -> v e. %s )' % (Av, UO))
    vc, vlo, vhi = uo_mem(w, Av, 'v', vin)
    affe_v = fv1(w, Av, 'y', UO, lambda q: '( ( %s x. %s ) + %s )' % (a1, q, b1), 'v', vin, 'ovex')
    rE = D(w, A, 'ralrimiva', [D(w, Av, 'eqeltrd', [affe_v, D(w, Av, 'addcld', [D(w, Av, 'mulcld', [ad(w, Av, D(w, A, 'halfcld', [lgc], '%s e. CC' % a1), '%s e. CC' % a1), vc], '( %s x. v ) e. CC' % a1),
                                                                               ad(w, Av, D(w, A, 'mulcld', [ph2, lgc], '%s e. CC' % b1), '%s e. CC' % b1)], '( ( %s x. v ) + %s ) e. CC' % (a1, b1))],
                                                 '( %s ` v ) e. CC' % AFE)], 'A. v e. %s ( %s ` v ) e. CC' % (UO, AFE))
    cE = D(w, A, 'syl3anc', [hol_exp(w, A), hE, rE, w.inst('zl3hco')], HOL('( z e. %s |-> ( exp ` ( %s ` z ) ) )' % (UO, AFE), UO))
    Fx = '( x e. %s |-> ( exp ` ( %s ` x ) ) )' % (UO, AFE)
    cEx = rebind(w, A, cE, lambda q: '( exp ` ( %s ` %s ) )' % (AFE, q), UO, 'z', 'x')
    affg_v = fv1(w, Av, 'y', UO, lambda q: '( ( %s x. %s ) + %s )' % (a2, q, b2), 'v', vin, 'ovex')
    rvr = D(w, Av, 'recld', [vc], '( Re ` v ) e. RR')
    clv = Closure(w, Av, {'( Re ` v )': ('RR', rvr), 'P': [('RR', ad(w, Av, pr, 'P e. RR')), ('ge0', ad(w, Av, p0, '0 <_ P'))]})
    ph2v = ad(w, Av, ph2, '( P / 2 ) e. CC')
    gval = '( ( %s x. v ) + %s )' % (a2, b2)
    gvc = D(w, Av, 'addcld', [D(w, Av, 'mulcld', [cst(w, Av, 'halfcn', '( 1 / 2 ) e. CC'), vc], '( ( 1 / 2 ) x. v ) e. CC'), ad(w, Av, D(w, A, 'addcld', [ph2, cst(w, A, 'ax-1cn', '1 e. CC')], '%s e. CC' % b2), '%s e. CC' % b2)],
             '%s e. CC' % gval)
    reg = chain(w, Av, ['( Re ` %s )' % gval, '( ( Re ` ( ( 1 / 2 ) x. v ) ) + ( Re ` %s ) )' % b2, '( ( ( 1 / 2 ) x. ( Re ` v ) ) + %s )' % b2],
                [D(w, Av, 'readdd', [D(w, Av, 'mulcld', [cst(w, Av, 'halfcn', '( 1 / 2 ) e. CC'), vc], '( ( 1 / 2 ) x. v ) e. CC'), ad(w, Av, D(w, A, 'addcld', [ph2, cst(w, A, 'ax-1cn', '1 e. CC')], '%s e. CC' % b2), '%s e. CC' % b2)],
                   '( Re ` %s ) = ( ( Re ` ( ( 1 / 2 ) x. v ) ) + ( Re ` %s ) )' % (gval, b2)),
                 D(w, Av, 'oveq12d', [D(w, Av, 'remul2d', [cst(w, Av, 'halfre', '( 1 / 2 ) e. RR'), vc], '( Re ` ( ( 1 / 2 ) x. v ) ) = ( ( 1 / 2 ) x. ( Re ` v ) )'),
                                      D(w, Av, 'rered', [clv.mem(b2, 'RR')], '( Re ` %s ) = %s' % (b2, b2))], '( ( Re ` ( ( 1 / 2 ) x. v ) ) + ( Re ` %s ) ) = ( ( ( 1 / 2 ) x. ( Re ` v ) ) + %s )' % (b2, b2))])
    gpos = D(w, Av, 'breqtrrd', [linarith(w, Av, [vlo, ad(w, Av, p0, '0 <_ P')], '0 < ( ( ( 1 / 2 ) x. ( Re ` v ) ) + %s )' % b2, closure=clv), reg], '0 < ( Re ` %s )' % gval)
    ghp = D(w, Av, 'mpbird', [D(w, Av, 'jca', [gvc, D(w, Av, 'jca', [gpos, D(w, Av, 'ltpnfd', [D(w, Av, 'recld', [gvc], '( Re ` %s ) e. RR' % gval)], '( Re ` %s ) < +oo' % gval)], '( 0 < ( Re ` %s ) /\\ ( Re ` %s ) < +oo )' % (gval, gval))],
                                           '( %s e. CC /\\ ( 0 < ( Re ` %s ) /\\ ( Re ` %s ) < +oo ) )' % (gval, gval, gval)),
                                   D(w, Av, 'syl2anc', [cst(w, Av, '0xr', '0 e. RR*'), cst(w, Av, 'pnfxr', '+oo e. RR*'), w.inst('z6melst')], '( %s e. %s <-> ( %s e. CC /\\ ( 0 < ( Re ` %s ) /\\ ( Re ` %s ) < +oo ) ) )' % (gval, HP0, gval, gval, gval))],
              '%s e. %s' % (gval, HP0))
    rG = D(w, A, 'ralrimiva', [D(w, Av, 'eqeltrd', [affg_v, ghp], '( %s ` v ) e. %s' % (AFG, HP0))], 'A. v e. %s ( %s ` v ) e. %s' % (UO, AFG, HP0))
    cG = D(w, A, 'syl3anc', [gam, hG, rG, w.inst('zl3hco')], HOL('( z e. %s |-> ( %s ` ( %s ` z ) ) )' % (UO, GAMy, AFG), UO))
    Gx = '( x e. %s |-> ( %s ` ( %s ` x ) ) )' % (UO, GAMy, AFG)
    cGx = rebind(w, A, cG, lambda q: '( %s ` ( %s ` %s ) )' % (GAMy, AFG, q), UO, 'z', 'x')
    # values at v
    Wv = LE.WV('v')
    wvc = D(w, Av, 'halfcld', [D(w, Av, 'addcld', [vc, ad(w, Av, pc, 'P e. CC')], '( v + P ) e. CC')], '%s e. CC' % Wv)
    galg = chain(w, Av, [gval, '( ( v / 2 ) + ( ( P / 2 ) + 1 ) )', '( ( ( v / 2 ) + ( P / 2 ) ) + 1 )', '( %s + 1 )' % Wv],
                 [D(w, Av, 'oveq1d', [D(w, Av, 'eqcomd', [D(w, Av, 'divrec2d', [vc, cst(w, Av, '2cn', '2 e. CC'), cst(w, Av, '2ne0', '2 =/= 0')], '( v / 2 ) = ( ( 1 / 2 ) x. v )')], '( ( 1 / 2 ) x. v ) = ( v / 2 )')],
                    '%s = ( ( v / 2 ) + ( ( P / 2 ) + 1 ) )' % gval),
                  ('r', D(w, Av, 'addassd', [D(w, Av, 'halfcld', [vc], '( v / 2 ) e. CC'), ph2v, cst(w, Av, 'ax-1cn', '1 e. CC')], '( ( ( v / 2 ) + ( P / 2 ) ) + 1 ) = ( ( v / 2 ) + ( ( P / 2 ) + 1 ) )')),
                  D(w, Av, 'oveq1d', [D(w, Av, 'eqcomd', [D(w, Av, 'divdird', [vc, ad(w, Av, pc, 'P e. CC'), cst(w, Av, '2cn', '2 e. CC'), cst(w, Av, '2ne0', '2 =/= 0')], '%s = ( ( v / 2 ) + ( P / 2 ) )' % Wv)],
                                                          '( ( v / 2 ) + ( P / 2 ) ) = %s' % Wv)], '( ( ( v / 2 ) + ( P / 2 ) ) + 1 ) = ( %s + 1 )' % Wv)])
    gxv = chain(w, Av, ['( %s ` v )' % Gx, '( %s ` ( %s ` v ) )' % (GAMy, AFG), '( %s ` %s )' % (GAMy, gval), '( _G ` %s )' % gval, '( _G ` ( %s + 1 ) )' % Wv],
                [fv1(w, Av, 'x', UO, lambda q: '( %s ` ( %s ` %s ) )' % (GAMy, AFG, q), 'v', vin, 'fvex'),
                 D(w, Av, 'fveq2d', [affg_v], '( %s ` ( %s ` v ) ) = ( %s ` %s )' % (GAMy, AFG, GAMy, gval)),
                 fv1(w, Av, 'y', HP0, GAMz, gval, ghp, 'fvex'),
                 D(w, Av, 'fveq2d', [galg], '( _G ` %s ) = ( _G ` ( %s + 1 ) )' % (gval, Wv))])
    eval_ = '( ( %s x. v ) + %s )' % (a1, b1)
    ealg = chain(w, Av, [eval_, '( ( ( v / 2 ) x. %s ) + ( ( P / 2 ) x. %s ) )' % (LG, LG), '( ( ( v / 2 ) + ( P / 2 ) ) x. %s )' % LG, '( %s x. %s )' % (Wv, LG)],
                 [D(w, Av, 'oveq1d', [D(w, Av, 'eqtrd', [D(w, Av, 'mulcomd', [ad(w, Av, D(w, A, 'halfcld', [lgc], '%s e. CC' % a1), '%s e. CC' % a1), vc], '( %s x. v ) = ( v x. %s )' % (a1, a1)),
                                                         D(w, Av, 'eqtr4d', [D(w, Av, 'div12d' if False else 'mul12d' if False else 'divassd' if False else 'mulcld', [], '') if False else
                                                                             D(w, Av, 'divassd' if False else 'eqtr3d', [D(w, Av, 'divassd', [vc, ad(w, Av, lgc, '%s e. CC' % LG), cst(w, Av, '2cn', '2 e. CC'), cst(w, Av, '2ne0', '2 =/= 0')],
                                                                                                                         '( ( v x. %s ) / 2 ) = ( v x. %s )' % (LG, a1)),
                                                                                                                       D(w, Av, 'div23d', [vc, ad(w, Av, lgc, '%s e. CC' % LG), cst(w, Av, '2cn', '2 e. CC'), cst(w, Av, '2ne0', '2 =/= 0')],
                                                                                                                         '( ( v x. %s ) / 2 ) = ( ( v / 2 ) x. %s )' % (LG, LG))],
                                                                               '( v x. %s ) = ( ( v / 2 ) x. %s )' % (a1, LG)),
                                                                             D(w, Av, 'eqidd', [], '( ( v / 2 ) x. %s ) = ( ( v / 2 ) x. %s )' % (LG, LG))], '( v x. %s ) = ( ( v / 2 ) x. %s )' % (a1, LG))],
                                    '( %s x. v ) = ( ( v / 2 ) x. %s )' % (a1, LG))], '%s = ( ( ( v / 2 ) x. %s ) + %s )' % (eval_, LG, b1)),
                  ('r', D(w, Av, 'adddird', [D(w, Av, 'halfcld', [vc], '( v / 2 ) e. CC'), ph2v, ad(w, Av, lgc, '%s e. CC' % LG)], '( ( ( v / 2 ) + ( P / 2 ) ) x. %s ) = ( ( ( v / 2 ) x. %s ) + ( ( P / 2 ) x. %s ) )' % (LG, LG, LG))),
                  D(w, Av, 'oveq1d', [D(w, Av, 'eqcomd', [D(w, Av, 'divdird', [vc, ad(w, Av, pc, 'P e. CC'), cst(w, Av, '2cn', '2 e. CC'), cst(w, Av, '2ne0', '2 =/= 0')], '%s = ( ( v / 2 ) + ( P / 2 ) )' % Wv)],
                                                          '( ( v / 2 ) + ( P / 2 ) ) = %s' % Wv)], '( ( ( v / 2 ) + ( P / 2 ) ) x. %s ) = ( %s x. %s )' % (LG, Wv, LG))])
    pmv = Closure(w, Av, {'M': ('NN', ad(w, Av, mn, 'M e. NN')), '_pi': ('RR+', cst(w, Av, 'pirp', '_pi e. RR+'))})
    fxv = chain(w, Av, ['( %s ` v )' % Fx, '( exp ` ( %s ` v ) )' % AFE, '( exp ` %s )' % eval_, '( exp ` ( %s x. %s ) )' % (Wv, LG), '( %s ^c %s )' % (PM, Wv)],
                [fv1(w, Av, 'x', UO, lambda q: '( exp ` ( %s ` %s ) )' % (AFE, q), 'v', vin, 'fvex'),
                 D(w, Av, 'fveq2d', [affe_v], '( exp ` ( %s ` v ) ) = ( exp ` %s )' % (AFE, eval_)),
                 D(w, Av, 'fveq2d', [ealg], '( exp ` %s ) = ( exp ` ( %s x. %s ) )' % (eval_, Wv, LG)),
                 ('r', D(w, Av, 'cxpefd', [pmv.mem(PM, 'CC'), pmv.ne0(PM), wvc], '( %s ^c %s ) = ( exp ` ( %s x. %s ) )' % (PM, Wv, Wv, LG)))])
    g1dm = D(w, Av, 'syl2anc', [D(w, Av, 'addcld', [wvc, cst(w, Av, 'ax-1cn', '1 e. CC')], '( %s + 1 ) e. CC' % Wv),
                                D(w, Av, 'breqtrd', [D(w, Av, 'breqtrd', [gpos, D(w, Av, 'fveq2d', [galg], '( Re ` %s ) = ( Re ` ( %s + 1 ) )' % (gval, Wv))], '0 < ( Re ` ( %s + 1 ) )' % Wv),
                                                     D(w, Av, 'eqidd', [], '( Re ` ( %s + 1 ) ) = ( Re ` ( %s + 1 ) )' % (Wv, Wv))], '0 < ( Re ` ( %s + 1 ) )' % Wv), w.inst('zrenn')],
               '( %s + 1 ) e. ( CC \\ ( ZZ \\ NN ) )' % Wv)
    gne = D(w, Av, 'eqnetrd', [gxv, D(w, Av, 'syl', [g1dm, w.inst('gamne0')], '( _G ` ( %s + 1 ) ) =/= 0' % Wv)], '( %s ` v ) =/= 0' % Gx)
    rne = D(w, A, 'ralrimiva', [gne], 'A. v e. %s ( %s ` v ) =/= 0' % (UO, Gx))
    dv = D(w, A, 'syl3anc', [cEx, cGx, rne, w.inst('holdiv')], HOL('( z e. %s |-> ( ( %s ` z ) / ( %s ` z ) ) )' % (UO, Fx, Gx), UO))
    DVb = lambda q: '( ( %s ` %s ) / ( %s ` %s ) )' % (Fx, q, Gx, q)
    dvv = rebind(w, A, dv, DVb, UO, 'z', 'v')
    hv_eq = D(w, Av, 'oveq12d', [fxv, gxv], '%s = %s' % (DVb('v'), LE.HV('v')))
    m1 = D(w, A, 'mpteq2dva', [hv_eq], '( v e. %s |-> %s ) = ( v e. %s |-> %s )' % (UO, DVb('v'), UO, LE.HV('v')))
    hvv = D(w, A, 'mpbid', [dvv, hol_eq(w, A, m1, '( v e. %s |-> %s )' % (UO, DVb('v')), '( v e. %s |-> %s )' % (UO, LE.HV('v')), UO)], HOL('( v e. %s |-> %s )' % (UO, LE.HV('v')), UO))
    Hx = '( x e. %s |-> %s )' % (UO, LE.HV('x'))
    hx = rebind(w, A, hvv, LE.HV, UO, 'v', 'x')
    # g = w h
    hW = aff_hol(w, A, '( 1 / 2 )', '( P / 2 )', cst(w, A, 'halfcn', '( 1 / 2 ) e. CC'), ph2, UO, opn)
    Wy = '( y e. %s |-> ( ( ( 1 / 2 ) x. y ) + ( P / 2 ) ) )' % UO
    ml = D(w, A, 'syl2anc', [hW, hx, w.inst('holmul')], HOL('( z e. %s |-> ( ( %s ` z ) x. ( %s ` z ) ) )' % (UO, Wy, Hx), UO))
    MLb = lambda q: '( ( %s ` %s ) x. ( %s ` %s ) )' % (Wy, q, Hx, q)
    mlv = rebind(w, A, ml, MLb, UO, 'z', 'v')
    wyv = fv1(w, Av, 'y', UO, lambda q: '( ( ( 1 / 2 ) x. %s ) + ( P / 2 ) )' % q, 'v', vin, 'ovex')
    walg = D(w, Av, 'eqtr4d', [D(w, Av, 'oveq1d', [D(w, Av, 'eqcomd', [D(w, Av, 'divrec2d', [vc, cst(w, Av, '2cn', '2 e. CC'), cst(w, Av, '2ne0', '2 =/= 0')], '( v / 2 ) = ( ( 1 / 2 ) x. v )')], '( ( 1 / 2 ) x. v ) = ( v / 2 )')],
                                                  '( ( ( 1 / 2 ) x. v ) + ( P / 2 ) ) = ( ( v / 2 ) + ( P / 2 ) )'),
                               D(w, Av, 'divdird', [vc, ad(w, Av, pc, 'P e. CC'), cst(w, Av, '2cn', '2 e. CC'), cst(w, Av, '2ne0', '2 =/= 0')], '%s = ( ( v / 2 ) + ( P / 2 ) )' % Wv)],
               '( ( ( 1 / 2 ) x. v ) + ( P / 2 ) ) = %s' % Wv)
    hxv = fv1(w, Av, 'x', UO, LE.HV, 'v', vin, 'ovex')
    gv_eq = D(w, Av, 'oveq12d', [D(w, Av, 'eqtrd', [wyv, walg], '( %s ` v ) = %s' % (Wy, Wv)), hxv], '%s = %s' % (MLb('v'), LE.GV('v')))
    m2 = D(w, A, 'mpteq2dva', [gv_eq], '( v e. %s |-> %s ) = ( v e. %s |-> %s )' % (UO, MLb('v'), UO, LE.GV('v')))
    gvv = D(w, A, 'mpbid', [mlv, hol_eq(w, A, m2, '( v e. %s |-> %s )' % (UO, MLb('v')), '( v e. %s |-> %s )' % (UO, LE.GV('v')), UO)], HOL('( v e. %s |-> %s )' % (UO, LE.GV('v')), UO))
    gx = rebind(w, A, gvv, LE.GV, UO, 'v', 'x')
    w.qed([D(w, A, 'jca', [hx, gx], Cc)], 'idi', SE['zl3ghl'])
    goe(w)


RA, RB = '( 0 + ( _i x. -u 1 ) )', '( 2 + ( _i x. 1 ) )'
RCT = '( %s crect %s )' % (RA, RB)


def rect_facts(w, A):
    """closed facts of the rectangle [ 0 , 2 ] x [ -1 , 1 ] under A"""
    n1 = cst(w, A, 'neg1rr', '-u 1 e. RR')
    r0, r1, r2 = cst(w, A, '0re', '0 e. RR'), cst(w, A, '1re', '1 e. RR'), cst(w, A, '2re', '2 e. RR')
    ra = D(w, A, 'syl2anc', [r0, n1, w.inst('crre')], '( Re ` %s ) = 0' % RA); ia = D(w, A, 'syl2anc', [r0, n1, w.inst('crim')], '( Im ` %s ) = -u 1' % RA)
    rb = D(w, A, 'syl2anc', [r2, r1, w.inst('crre')], '( Re ` %s ) = 2' % RB); ib = D(w, A, 'syl2anc', [r2, r1, w.inst('crim')], '( Im ` %s ) = 1' % RB)
    ac = D(w, A, 'addcld', [cst(w, A, '0cn', '0 e. CC'), D(w, A, 'mulcld', [cst(w, A, 'ax-icn', '_i e. CC'), cst(w, A, 'neg1cn', '-u 1 e. CC')], '( _i x. -u 1 ) e. CC')], '%s e. CC' % RA)
    bc = D(w, A, 'addcld', [cst(w, A, '2cn', '2 e. CC'), D(w, A, 'mulcld', [cst(w, A, 'ax-icn', '_i e. CC'), cst(w, A, 'ax-1cn', '1 e. CC')], '( _i x. 1 ) e. CC')], '%s e. CC' % RB)
    return dict(ra=ra, ia=ia, rb=rb, ib=ib, ac=ac, bc=bc)


def rect_mem(w, Au, u, R):
    """( Au -> u e. RCT ) -> u e. CC , 0 <_ Re u <_ 2 , -1 <_ Im u <_ 1 : returns the elcrect equivalence"""
    return D(w, Au, 'syl2anc', [R['ac'], R['bc'], w.inst('elcrect')],
             '( %s e. %s <-> ( %s e. CC /\\ ( Re ` %s ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ ( Im ` %s ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) ) )' % (u, RCT, u, u, RA, RB, u, RA, RB))


# ---------------------------------------------------------------- zl3dq
if wante('zl3dq', MAIN):
    w = W('zl3dq', 'The difference quotient ` DQ ( v ) = ( g ( v ) - g ( 1 ) ) / ( v - 1 ) ` , extended by ` g \' ( 1 ) ` , is holomorphic on ` U ` ( ~ zl3rem on the rectangle ` [ 0 , 2 ] x [ -1 , 1 ] ` ) and bounded on the strip by ` c + abs g ( v ) + abs g ( 1 ) ` .')
    A, Cc = ante_e('zl3dq')
    ghl = D(w, A, 'syl', [w.s([], 'id', '( %s -> %s )' % (A, A)), w.inst('zl3ghl')], L.split_imp(SE['zl3ghl'])[1])
    Gx = '( x e. %s |-> %s )' % (UO, LE.GV('x'))
    hg = D(w, A, 'simprd', [ghl], HOL(Gx, UO))
    gf = D(w, A, 'syl', [D(w, A, 'simpld', [hg], '%s e. ( %s -cn-> CC )' % (Gx, UO)), w.inst('cncff')], '%s : %s --> CC' % (Gx, UO))
    R = rect_facts(w, A)
    one_u = D(w, A, 'mpbird', [D(w, A, 'jca', [cst(w, A, 'ax-1cn', '1 e. CC'), D(w, A, 'jca', [D(w, A, 'breqtrrd', [cst(w, A, 'neg1lt0', '-u 1 < 0'), D(w, A, 'eqidd', [], '0 = 0')], '-u 1 < 0') and
                                                                                     D(w, A, 'breqtrrd', [cst(w, A, 'neg1lt0', '-u 1 < 0') and D(w, A, 'lttrd', [cst(w, A, 'neg1rr', '-u 1 e. RR'), cst(w, A, '0re', '0 e. RR'), cst(w, A, '1re', '1 e. RR'), cst(w, A, 'neg1lt0', '-u 1 < 0'), cst(w, A, '0lt1', '0 < 1')], '-u 1 < 1'),
                                                                                                            cst(w, A, 're1', '( Re ` 1 ) = 1')], '-u 1 < ( Re ` 1 )'),
                                                                                     D(w, A, 'eqbrtrd', [cst(w, A, 're1', '( Re ` 1 ) = 1'), cst(w, A, '1lt3', '1 < 3')], '( Re ` 1 ) < 3')], '( -u 1 < ( Re ` 1 ) /\\ ( Re ` 1 ) < 3 )')],
                                              '( 1 e. CC /\\ ( -u 1 < ( Re ` 1 ) /\\ ( Re ` 1 ) < 3 ) )'),
                               D(w, A, 'syl2anc', [D(w, A, 'rexrd', [cst(w, A, 'neg1rr', '-u 1 e. RR')], '-u 1 e. RR*'), D(w, A, 'rexrd', [cst(w, A, '3re', '3 e. RR')], '3 e. RR*'), w.inst('z6melst')],
                                 '( 1 e. %s <-> ( 1 e. CC /\\ ( -u 1 < ( Re ` 1 ) /\\ ( Re ` 1 ) < 3 ) ) )' % UO)], '1 e. %s' % UO)
    g1v = D(w, A, 'eqtr3d', [fv1(w, A, 'x', UO, LE.GV, '1', one_u, 'ovex'), D(w, A, 'eqidd', [], '%s = %s' % (LE.GV('1'), LE.GV('1')))], '( %s ` 1 ) = %s' % (Gx, LE.GV('1'))) if False else \
        fv1(w, A, 'x', UO, LE.GV, '1', one_u, 'ovex')
    g1c = D(w, A, 'eqeltrrd', [g1v, D(w, A, 'ffvelcdmd', [gf, one_u], '( %s ` 1 ) e. CC' % Gx)], '%s e. CC' % LE.GV('1'))
    G1 = LE.GV('1')
    opn = uo_facts(w, A)
    hC = aff_hol(w, A, '0', G1, cst(w, A, '0cn', '0 e. CC'), g1c, UO, opn)
    Cy = '( y e. %s |-> ( ( 0 x. y ) + %s ) )' % (UO, G1)
    sb = D(w, A, 'syl2anc', [hg, hC, w.inst('zl2hsub')], HOL('( z e. %s |-> ( ( %s ` z ) - ( %s ` z ) ) )' % (UO, Gx, Cy), UO))
    SBb = lambda q: '( ( %s ` %s ) - ( %s ` %s ) )' % (Gx, q, Cy, q)
    sbx = rebind(w, A, sb, SBb, UO, 'z', 'x')
    Av = '( %s /\\ v e. %s )' % (A, UO)
    vin = w.s([], 'simpr', '( %s -> v e. %s )' % (Av, UO))
    vc, vlo, vhi = uo_mem(w, Av, 'v', vin)
    g1cv = ad(w, Av, g1c, '%s e. CC' % G1)
    gvv = fv1(w, Av, 'x', UO, LE.GV, 'v', vin, 'ovex')
    cyv = D(w, Av, 'eqtrd', [fv1(w, Av, 'y', UO, lambda q: '( ( 0 x. %s ) + %s )' % (q, G1), 'v', vin, 'ovex'),
                             D(w, Av, 'eqtrd', [D(w, Av, 'oveq1d', [D(w, Av, 'mul02d', [vc], '( 0 x. v ) = 0')], '( ( 0 x. v ) + %s ) = ( 0 + %s )' % (G1, G1)), D(w, Av, 'addlidd', [g1cv], '( 0 + %s ) = %s' % (G1, G1))],
                               '( ( 0 x. v ) + %s ) = %s' % (G1, G1))], '( %s ` v ) = %s' % (Cy, G1))
    GMb = lambda q: '( %s - %s )' % (LE.GV(q), G1)
    me = D(w, A, 'mpteq2dva', [D(w, Av, 'oveq12d', [gvv, cyv], '%s = %s' % (SBb('v'), GMb('v')))], '( v e. %s |-> %s ) = ( v e. %s |-> %s )' % (UO, SBb('v'), UO, GMb('v')))
    sbv = rebind(w, A, sb, SBb, UO, 'z', 'v')
    gmv = D(w, A, 'mpbid', [sbv, hol_eq(w, A, me, '( v e. %s |-> %s )' % (UO, SBb('v')), '( v e. %s |-> %s )' % (UO, GMb('v')), UO)], HOL('( v e. %s |-> %s )' % (UO, GMb('v')), UO))
    GM = LE.GM()
    assert GM == '( x e. %s |-> %s )' % (UO, GMb('x'))
    hgm = rebind(w, A, gmv, GMb, UO, 'v', 'x')
    gm1 = D(w, A, 'eqtrd', [fv1(w, A, 'x', UO, GMb, '1', one_u, 'ovex'), D(w, A, 'subidd', [g1c], '%s = 0' % GMb('1'))], '( %s ` 1 ) = 0' % GM)
    # the rectangle in U
    Au = '( %s /\\ u e. %s )' % (A, RCT)
    Rl = lambda k, f: ad(w, Au, R[k], f)
    RR_ = {'ac': Rl('ac', '%s e. CC' % RA), 'bc': Rl('bc', '%s e. CC' % RB)}
    uR = D(w, Au, 'mpbid', [w.s([], 'simpr', '( %s -> u e. %s )' % (Au, RCT)), rect_mem(w, Au, 'u', RR_)],
           '( u e. CC /\\ ( Re ` u ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ ( Im ` u ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) )' % (RA, RB, RA, RB))
    ucc = D(w, Au, 'simp1d', [uR], 'u e. CC')
    ure = D(w, Au, 'eleqtrd', [D(w, Au, 'simp2d', [uR], '( Re ` u ) e. ( ( Re ` %s ) [,] ( Re ` %s ) )' % (RA, RB)),
                               D(w, Au, 'oveq12d', [Rl('ra', '( Re ` %s ) = 0' % RA), Rl('rb', '( Re ` %s ) = 2' % RB)], '( ( Re ` %s ) [,] ( Re ` %s ) ) = ( 0 [,] 2 )' % (RA, RB))], '( Re ` u ) e. ( 0 [,] 2 )')
    ub = D(w, Au, 'mpbid', [ure, D(w, Au, 'syl2anc', [cst(w, Au, '0re', '0 e. RR'), cst(w, Au, '2re', '2 e. RR'), w.inst('elicc2')], '( ( Re ` u ) e. ( 0 [,] 2 ) <-> ( ( Re ` u ) e. RR /\\ 0 <_ ( Re ` u ) /\\ ( Re ` u ) <_ 2 ) )')],
           '( ( Re ` u ) e. RR /\\ 0 <_ ( Re ` u ) /\\ ( Re ` u ) <_ 2 )')
    clu = Closure(w, Au, {'( Re ` u )': ('RR', D(w, Au, 'simp1d', [ub], '( Re ` u ) e. RR'))})
    uU = D(w, Au, 'mpbird', [D(w, Au, 'jca', [ucc, D(w, Au, 'jca', [linarith(w, Au, [D(w, Au, 'simp2d', [ub], '0 <_ ( Re ` u )')], '-u 1 < ( Re ` u )', closure=clu),
                                                                  linarith(w, Au, [D(w, Au, 'simp3d', [ub], '( Re ` u ) <_ 2')], '( Re ` u ) < 3', closure=clu)], '( -u 1 < ( Re ` u ) /\\ ( Re ` u ) < 3 )')],
                                         '( u e. CC /\\ ( -u 1 < ( Re ` u ) /\\ ( Re ` u ) < 3 ) )'),
                             D(w, Au, 'syl2anc', [D(w, Au, 'rexrd', [cst(w, Au, 'neg1rr', '-u 1 e. RR')], '-u 1 e. RR*'), D(w, Au, 'rexrd', [cst(w, Au, '3re', '3 e. RR')], '3 e. RR*'), w.inst('z6melst')],
                               '( u e. %s <-> ( u e. CC /\\ ( -u 1 < ( Re ` u ) /\\ ( Re ` u ) < 3 ) ) )' % UO)], 'u e. %s' % UO)
    rss = D(w, A, 'ssrdv', [D(w, A, 'ex', [uU], '( u e. %s -> u e. %s )' % (RCT, UO))], '%s C_ %s' % (RCT, UO))
    lt = lambda a, b, st: st
    ins = D(w, A, 'jca', [cst(w, A, 'ax-1cn', '1 e. CC'),
                          D(w, A, 'jca', [D(w, A, 'jca', [D(w, A, 'eqbrtrd', [R['ra'], D(w, A, 'breqtrrd', [cst(w, A, '0lt1', '0 < 1'), cst(w, A, 're1', '( Re ` 1 ) = 1')], '0 < ( Re ` 1 )')], '( Re ` %s ) < ( Re ` 1 )' % RA),
                                                          D(w, A, 'breqtrrd', [D(w, A, 'eqbrtrd', [cst(w, A, 're1', '( Re ` 1 ) = 1'), cst(w, A, '1lt2', '1 < 2')], '( Re ` 1 ) < 2'), R['rb']], '( Re ` 1 ) < ( Re ` %s )' % RB)],
                                          '( ( Re ` %s ) < ( Re ` 1 ) /\\ ( Re ` 1 ) < ( Re ` %s ) )' % (RA, RB)),
                                          D(w, A, 'jca', [D(w, A, 'eqbrtrd', [R['ia'], D(w, A, 'breqtrrd', [cst(w, A, 'neg1lt0', '-u 1 < 0'), cst(w, A, 'im1', '( Im ` 1 ) = 0')], '-u 1 < ( Im ` 1 )')], '( Im ` %s ) < ( Im ` 1 )' % RA),
                                                          D(w, A, 'breqtrrd', [D(w, A, 'eqbrtrd', [cst(w, A, 'im1', '( Im ` 1 ) = 0'), cst(w, A, '0lt1', '0 < 1')], '( Im ` 1 ) < 1'), R['ib']], '( Im ` 1 ) < ( Im ` %s )' % RB)],
                                            '( ( Im ` %s ) < ( Im ` 1 ) /\\ ( Im ` 1 ) < ( Im ` %s ) )' % (RA, RB))],
                            '( ( ( Re ` %s ) < ( Re ` 1 ) /\\ ( Re ` 1 ) < ( Re ` %s ) ) /\\ ( ( Im ` %s ) < ( Im ` 1 ) /\\ ( Im ` 1 ) < ( Im ` %s ) ) )' % (RA, RB, RA, RB))],
              '( 1 e. CC /\\ ( ( ( Re ` %s ) < ( Re ` 1 ) /\\ ( Re ` 1 ) < ( Re ` %s ) ) /\\ ( ( Im ` %s ) < ( Im ` 1 ) /\\ ( Im ` 1 ) < ( Im ` %s ) ) ) )' % (RA, RB, RA, RB))
    RECTi = LE.tsub(LE.RECT, {'A': RA, 'B': RB, 'P': '1', 'D': UO})
    rect = D(w, A, 'jca', [D(w, A, 'jca', [D(w, A, 'jca', [R['ac'], R['bc']], '( %s e. CC /\\ %s e. CC )' % (RA, RB)), ins], RECTi[2:RECTi.rindex(' /\\ ( %s crect' % RA)]), rss], RECTi)
    DQ = LE.DQ()
    assert LE.tsub(LE.QR, {'G': GM, 'D': UO, 'P': '1'}) == DQ
    hdq = D(w, A, 'syl3anc', [hgm, rect, gm1, w.inst('zl3rem')], HOL(DQ, UO))
    D1 = '( ( CC _D %s ) ` 1 )' % GM
    DQb = lambda q: 'if ( %s = 1 , %s , ( ( %s ` %s ) / ( %s - 1 ) ) )' % (q, D1, GM, q, q)
    assert DQ == '( u e. %s |-> %s )' % (UO, DQb('u'))
    vexq = lambda q: ('ifex', [w.s([], 'fvex', '%s e. _V' % D1), w.s([], 'ovex', '( ( %s ` %s ) / ( %s - 1 ) ) e. _V' % (GM, q, q))])
    Avn = '( %s /\\ v =/= 1 )' % Av
    vinn = ad(w, Avn, vin, 'v e. %s' % UO)
    dqv = chain(w, Avn, ['( %s ` v )' % DQ, DQb('v'), '( ( %s ` v ) / ( v - 1 ) )' % GM, '( %s / ( v - 1 ) )' % GMb('v')],
                [fv1(w, Avn, 'u', UO, DQb, 'v', vinn, vexq('v')),
                 D(w, Avn, 'iffalsed', [D(w, Avn, 'neneqd', [w.s([], 'simpr', '( %s -> v =/= 1 )' % Avn)], '-. v = 1')], '%s = ( ( %s ` v ) / ( v - 1 ) )' % (DQb('v'), GM)),
                 D(w, Avn, 'oveq1d', [fv1(w, Avn, 'x', UO, GMb, 'v', vinn, 'ovex')], '( ( %s ` v ) / ( v - 1 ) ) = ( %s / ( v - 1 ) )' % (GM, GMb('v')))])
    VAL = '( v =/= 1 -> ( %s ` v ) = ( %s / ( v - 1 ) ) )' % (DQ, GMb('v'))
    ralv = D(w, A, 'ralrimiva', [D(w, Av, 'ex', [dqv], VAL)], 'A. v e. %s %s' % (UO, VAL))
    part1 = D(w, A, 'jca', [hdq, ralv], '( %s /\\ A. v e. %s %s )' % (HOL(DQ, UO), UO, VAL))
    BNu = 'A. q e. %s ( abs ` ( %s ` q ) ) <_ m' % (RCT, DQ)
    DQr = '( r e. %s |-> %s )' % (UO, DQb('r'))
    cbr = w.s([vsub(w, DQb, 'u', 'r')], 'cbvmptv', '%s = %s' % (DQ, DQr))
    dqrc = D(w, A, 'eqeltrrd', [w.s([cbr], 'a1i', '( %s -> %s = %s )' % (A, DQ, DQr)), D(w, A, 'simpld', [hdq], '%s e. ( %s -cn-> CC )' % (DQ, UO))], '%s e. ( %s -cn-> CC )' % (DQr, UO))
    BNr = 'A. u e. %s ( abs ` ( %s ` u ) ) <_ m' % (RCT, DQr)
    exr = D(w, A, 'syl2anc', [D(w, A, 'jca', [R['ac'], R['bc']], '( %s e. CC /\\ %s e. CC )' % (RA, RB)), D(w, A, 'jca', [dqrc, rss],
                                                                                                   '( %s e. ( %s -cn-> CC ) /\\ %s C_ %s )' % (DQr, UO, RCT, UO)), w.inst('crectbnd')], 'E. m e. RR %s' % BNr)
    BNrq = 'A. q e. %s ( abs ` ( %s ` q ) ) <_ m' % (RCT, DQr)
    cvq = w.s([w.s([w.s([w.s([], 'fveq2', '( u = q -> ( %s ` u ) = ( %s ` q ) )' % (DQr, DQr))], 'fveq2d', '( u = q -> ( abs ` ( %s ` u ) ) = ( abs ` ( %s ` q ) ) )' % (DQr, DQr))], 'breq1d',
                    '( u = q -> ( ( abs ` ( %s ` u ) ) <_ m <-> ( abs ` ( %s ` q ) ) <_ m ) )' % (DQr, DQr))], 'cbvralvw', '( %s <-> %s )' % (BNr, BNrq))
    bi0 = w.s([w.s([w.s([w.s([w.s([cbr], 'eqcomi', '%s = %s' % (DQr, DQ))], 'fveq1i', '( %s ` q ) = ( %s ` q )' % (DQr, DQ))], 'fveq2i', '( abs ` ( %s ` q ) ) = ( abs ` ( %s ` q ) )' % (DQr, DQ))],
                        'breq1i', '( ( abs ` ( %s ` q ) ) <_ m <-> ( abs ` ( %s ` q ) ) <_ m )' % (DQr, DQ))], 'ralbii', '( %s <-> %s )' % (BNrq, BNu))
    bi = w.s([cvq, bi0], 'bitri', '( %s <-> %s )' % (BNr, BNu))
    exm = D(w, A, 'mpbid', [exr, w.s([w.s([bi], 'rexbii', '( E. m e. RR %s <-> E. m e. RR %s )' % (BNr, BNu))], 'a1i', '( %s -> ( E. m e. RR %s <-> E. m e. RR %s ) )' % (A, BNr, BNu))],
            'E. m e. RR %s' % BNu)
    Am = '( %s /\\ ( m e. RR /\\ %s ) )' % (A, BNu)
    mr = D(w, Am, 'simprl', [], 'm e. RR'); bnu = D(w, Am, 'simprr', [], BNu)
    LA = lambda st, f: ad(w, Am, st, f)
    dqf = D(w, Am, 'syl', [D(w, Am, 'simpld', [LA(hdq, HOL(DQ, UO))], '%s e. ( %s -cn-> CC )' % (DQ, UO)), w.inst('cncff')], '%s : %s --> CC' % (DQ, UO))
    subu = lambda q: w.s([w.s([w.s([], 'fveq2', '( q = %s -> ( %s ` q ) = ( %s ` %s ) )' % (q, DQ, DQ, q))], 'fveq2d', '( q = %s -> ( abs ` ( %s ` q ) ) = ( abs ` ( %s ` %s ) ) )' % (q, DQ, DQ, q))], 'breq1d',
                         '( q = %s -> ( ( abs ` ( %s ` q ) ) <_ m <-> ( abs ` ( %s ` %s ) ) <_ m ) )' % (q, DQ, DQ, q))
    one_r = D(w, Am, 'syl', [D(w, Am, 'jca', [D(w, Am, 'jca', [LA(R['ac'], '%s e. CC' % RA), LA(R['bc'], '%s e. CC' % RB)], '( %s e. CC /\\ %s e. CC )' % (RA, RB)), LA(ins, LE.tsub(LE.RECT, {'A': RA, 'B': RB, 'P': '1', 'D': UO})[RECTi.index('( 1 e. CC'):RECTi.rindex(' ) /\\ ( %s crect' % RA)])],
                                      RECTi[2:RECTi.rindex(' /\\ ( %s crect' % RA)]), w.inst('crectinp')], '1 e. %s' % RCT)
    b1 = D(w, Am, 'mpd', [bnu, D(w, Am, 'syl', [one_r, w.s([subu('1')], 'rspcv', '( 1 e. %s -> ( %s -> ( abs ` ( %s ` 1 ) ) <_ m ) )' % (RCT, BNu, DQ))], '( %s -> ( abs ` ( %s ` 1 ) ) <_ m )' % (BNu, DQ))],
           '( abs ` ( %s ` 1 ) ) <_ m' % DQ)
    dq1c = D(w, Am, 'ffvelcdmd', [dqf, LA(one_u, '1 e. %s' % UO)], '( %s ` 1 ) e. CC' % DQ)
    m0 = D(w, Am, 'letrd', [cst(w, Am, '0re', '0 e. RR'), D(w, Am, 'abscld', [dq1c], '( abs ` ( %s ` 1 ) ) e. RR' % DQ), mr, D(w, Am, 'absge0d', [dq1c], '0 <_ ( abs ` ( %s ` 1 ) )' % DQ), b1], '0 <_ m')
    Av2 = '( %s /\\ v e. %s )' % (Am, STR)
    vs = w.s([], 'simpr', '( %s -> v e. %s )' % (Av2, STR))
    vst = D(w, Av2, 'sylib', [vs, w.inst('elstr')], '( v e. CC /\\ ( Re ` v ) e. ( -u ( 1 / 2 ) [,] 2 ) )')
    vc2 = D(w, Av2, 'simpld', [vst], 'v e. CC')
    vre = D(w, Av2, 'mpbid', [D(w, Av2, 'simprd', [vst], '( Re ` v ) e. ( -u ( 1 / 2 ) [,] 2 )'),
                              D(w, Av2, 'syl2anc', [Closure(w, Av2, {}).mem('-u ( 1 / 2 )', 'RR'), cst(w, Av2, '2re', '2 e. RR'), w.inst('elicc2')],
                                '( ( Re ` v ) e. ( -u ( 1 / 2 ) [,] 2 ) <-> ( ( Re ` v ) e. RR /\\ -u ( 1 / 2 ) <_ ( Re ` v ) /\\ ( Re ` v ) <_ 2 ) )')],
          '( ( Re ` v ) e. RR /\\ -u ( 1 / 2 ) <_ ( Re ` v ) /\\ ( Re ` v ) <_ 2 )')
    rvr = D(w, Av2, 'simp1d', [vre], '( Re ` v ) e. RR')
    cl2 = Closure(w, Av2, {'( Re ` v )': ('RR', rvr)})
    vU = D(w, Av2, 'mpbird', [D(w, Av2, 'jca', [vc2, D(w, Av2, 'jca', [linarith(w, Av2, [D(w, Av2, 'simp2d', [vre], '-u ( 1 / 2 ) <_ ( Re ` v )')], '-u 1 < ( Re ` v )', closure=cl2),
                                                                     linarith(w, Av2, [D(w, Av2, 'simp3d', [vre], '( Re ` v ) <_ 2')], '( Re ` v ) < 3', closure=cl2)], '( -u 1 < ( Re ` v ) /\\ ( Re ` v ) < 3 )')],
                                           '( v e. CC /\\ ( -u 1 < ( Re ` v ) /\\ ( Re ` v ) < 3 ) )'),
                               D(w, Av2, 'syl2anc', [D(w, Av2, 'rexrd', [cst(w, Av2, 'neg1rr', '-u 1 e. RR')], '-u 1 e. RR*'), D(w, Av2, 'rexrd', [cst(w, Av2, '3re', '3 e. RR')], '3 e. RR*'), w.inst('z6melst')],
                                 '( v e. %s <-> ( v e. CC /\\ ( -u 1 < ( Re ` v ) /\\ ( Re ` v ) < 3 ) ) )' % UO)], 'v e. %s' % UO)
    L2 = lambda st, f: ad(w, Av2, st, f)
    gvc2 = D(w, Av2, 'eqeltrrd', [fv1(w, Av2, 'x', UO, LE.GV, 'v', vU, 'ovex'), D(w, Av2, 'ffvelcdmd', [L2(LA(gf, '%s : %s --> CC' % (Gx, UO)), '%s : %s --> CC' % (Gx, UO)), vU], '( %s ` v ) e. CC' % Gx)],
             '%s e. CC' % LE.GV('v'))
    g1c2 = L2(LA(g1c, '%s e. CC' % G1), '%s e. CC' % G1)
    agv, ag1 = '( abs ` %s )' % LE.GV('v'), '( abs ` %s )' % G1
    T = '( m + ( %s + %s ) )' % (agv, ag1)
    agvr, ag1r = D(w, Av2, 'abscld', [gvc2], '%s e. RR' % agv), D(w, Av2, 'abscld', [g1c2], '%s e. RR' % ag1)
    agv0, ag10 = D(w, Av2, 'absge0d', [gvc2], '0 <_ %s' % agv), D(w, Av2, 'absge0d', [g1c2], '0 <_ %s' % ag1)
    mr2, m02 = L2(mr, 'm e. RR'), L2(m0, '0 <_ m')
    dqvc = D(w, Av2, 'ffvelcdmd', [L2(dqf, '%s : %s --> CC' % (DQ, UO)), vU], '( %s ` v ) e. CC' % DQ)
    adq = '( abs ` ( %s ` v ) )' % DQ
    adqr = D(w, Av2, 'abscld', [dqvc], '%s e. RR' % adq)
    vm1 = '( v - 1 )'
    vm1c = D(w, Av2, 'subcld', [vc2, cst(w, Av2, 'ax-1cn', '1 e. CC')], '%s e. CC' % vm1)
    av1 = '( abs ` %s )' % vm1
    av1r = D(w, Av2, 'abscld', [vm1c], '%s e. RR' % av1)
    cl3 = Closure(w, Av2, {'m': ('RR', mr2), agv: [('RR', agvr), ('ge0', agv0)], ag1: [('RR', ag1r), ('ge0', ag10)]})
    # case 1 <_ | v - 1 |
    A3 = '( %s /\\ 1 <_ %s )' % (Av2, av1)
    L3 = lambda st, f: ad(w, A3, st, f)
    d1 = w.s([], 'simpr', '( %s -> 1 <_ %s )' % (A3, av1))
    vm1c3 = L3(vm1c, '%s e. CC' % vm1)
    apos = D(w, A3, 'ltletrd', [cst(w, A3, '0re', '0 e. RR'), cst(w, A3, '1re', '1 e. RR'), L3(av1r, '%s e. RR' % av1), cst(w, A3, '0lt1', '0 < 1'), d1], '0 < %s' % av1)
    vne0 = D(w, A3, 'mpbird', [apos, D(w, A3, 'syl', [vm1c3, w.inst('absgt0')], '( %s =/= 0 <-> 0 < %s )' % (vm1, av1))], '%s =/= 0' % vm1)
    vne1 = D(w, A3, 'mpbid', [vne0, D(w, A3, 'necon3bid', [D(w, A3, 'subeq0ad', [L3(vc2, 'v e. CC'), cst(w, A3, 'ax-1cn', '1 e. CC')], '( %s = 0 <-> v = 1 )' % vm1)], '( %s =/= 0 <-> v =/= 1 )' % vm1)], 'v =/= 1')
    vU3 = L3(vU, 'v e. %s' % UO)
    rv = w.s([ralv], 'r19.21bi', '( %s -> %s )' % (Av, VAL))
    dqv3 = D(w, A3, 'mpd', [vne1, D(w, A3, 'syl2anc' if False else 'sylc' if False else 'syl', [D(w, A3, 'jca', [ad(w, A3, ad(w, Av2, ad(w, Am, cst(w, A, 'idi', '') if False else w.s([], 'idi', '') if False else None, ''), ''), '') if False else None, vU3], '') if False else None, None], '') if False else None], '') if False else None
    AvA = w.s([], 'id', '( %s -> %s )' % (A, A)) if False else None
    toAv = D(w, A3, 'jca', [ad(w, A3, ad(w, Av2, w.s([], 'simpl', '( %s -> %s )' % (Am, A)), A), A), vU3], Av)
    dqv3 = D(w, A3, 'mpd', [vne1, D(w, A3, 'syl', [toAv, rv], VAL)], '( %s ` v ) = ( %s / %s )' % (DQ, GMb('v'), vm1))
    X = '( abs ` %s )' % GMb('v')
    gmc = D(w, A3, 'subcld', [L3(gvc2, '%s e. CC' % LE.GV('v')), L3(g1c2, '%s e. CC' % G1)], '%s e. CC' % GMb('v'))
    xr, x0 = D(w, A3, 'abscld', [gmc], '%s e. RR' % X), D(w, A3, 'absge0d', [gmc], '0 <_ %s' % X)
    e1 = D(w, A3, 'eqtrd', [D(w, A3, 'fveq2d', [dqv3], '%s = ( abs ` ( %s / %s ) )' % (adq, GMb('v'), vm1)), D(w, A3, 'absdivd', [gmc, vm1c3, vne0], '( abs ` ( %s / %s ) ) = ( %s / %s )' % (GMb('v'), vm1, X, av1))],
           '%s = ( %s / %s )' % (adq, X, av1))
    cl4 = Closure(w, A3, {X: [('RR', xr), ('ge0', x0)], av1: ('RR', L3(av1r, '%s e. RR' % av1))})
    xle = D(w, A3, 'mpbird', [nlinarith(w, A3, [d1, x0], '%s <_ ( %s x. %s )' % (X, av1, X), closure=cl4, atoms=[X, av1]),
                              D(w, A3, 'ledivmuld', [xr, xr, D(w, A3, 'elrpd', [L3(av1r, '%s e. RR' % av1), apos], '%s e. RR+' % av1)], '( ( %s / %s ) <_ %s <-> %s <_ ( %s x. %s ) )' % (X, av1, X, X, av1, X))],
            '( %s / %s ) <_ %s' % (X, av1, X))
    tri = D(w, A3, 'abs2dif2d', [L3(gvc2, '%s e. CC' % LE.GV('v')), L3(g1c2, '%s e. CC' % G1)], '%s <_ ( %s + %s )' % (X, agv, ag1))
    cl5 = Closure(w, A3, {'m': [('RR', L3(mr2, 'm e. RR')), ('ge0', L3(m02, '0 <_ m'))], agv: [('RR', L3(agvr, '%s e. RR' % agv))], ag1: [('RR', L3(ag1r, '%s e. RR' % ag1))],
                          X: ('RR', xr), '( %s / %s )' % (X, av1): ('RR', D(w, A3, 'redivcld', [xr, L3(av1r, '%s e. RR' % av1), D(w, A3, 'gt0ne0d', [apos], '%s =/= 0' % av1)], '( %s / %s ) e. RR' % (X, av1)))})
    c1 = D(w, A3, 'eqbrtrd', [e1, linarith(w, A3, [xle, tri, L3(m02, '0 <_ m')], '( %s / %s ) <_ %s' % (X, av1, T), closure=cl5, atoms=[X, agv, ag1, 'm', '( %s / %s )' % (X, av1)])], '%s <_ %s' % (adq, T))
    # case | v - 1 | < 1
    A4 = '( %s /\\ %s < 1 )' % (Av2, av1)
    L4 = lambda st, f: ad(w, A4, st, f)
    d2 = w.s([], 'simpr', '( %s -> %s < 1 )' % (A4, av1))
    vc4, vm1c4 = L4(vc2, 'v e. CC'), L4(vm1c, '%s e. CC' % vm1)
    one4 = cst(w, A4, 'ax-1cn', '1 e. CC')
    rsub = D(w, A4, 'eqtrd', [D(w, A4, 'resubd', [vc4, one4], '( Re ` %s ) = ( ( Re ` v ) - ( Re ` 1 ) )' % vm1), D(w, A4, 'oveq2d', [cst(w, A4, 're1', '( Re ` 1 ) = 1')], '( ( Re ` v ) - ( Re ` 1 ) ) = ( ( Re ` v ) - 1 )')],
             '( Re ` %s ) = ( ( Re ` v ) - 1 )' % vm1)
    isub = D(w, A4, 'eqtrd', [D(w, A4, 'imsubd', [vc4, one4], '( Im ` %s ) = ( ( Im ` v ) - ( Im ` 1 ) )' % vm1),
                              D(w, A4, 'eqtrd', [D(w, A4, 'oveq2d', [cst(w, A4, 'im1', '( Im ` 1 ) = 0')], '( ( Im ` v ) - ( Im ` 1 ) ) = ( ( Im ` v ) - 0 )'),
                                                 D(w, A4, 'subid1d', [D(w, A4, 'recnd', [D(w, A4, 'imcld', [vc4], '( Im ` v ) e. RR')], '( Im ` v ) e. CC')], '( ( Im ` v ) - 0 ) = ( Im ` v )')],
                                '( ( Im ` v ) - ( Im ` 1 ) ) = ( Im ` v )')], '( Im ` %s ) = ( Im ` v )' % vm1)
    rlt = D(w, A4, 'lelttrd', [D(w, A4, 'abscld', [D(w, A4, 'recnd', [D(w, A4, 'recld', [vm1c4], '( Re ` %s ) e. RR' % vm1)], '( Re ` %s ) e. CC' % vm1)], '( abs ` ( Re ` %s ) ) e. RR' % vm1),
                               L4(av1r, '%s e. RR' % av1), cst(w, A4, '1re', '1 e. RR'), D(w, A4, 'syl', [vm1c4, w.inst('absrele')], '( abs ` ( Re ` %s ) ) <_ %s' % (vm1, av1)), d2],
            '( abs ` ( Re ` %s ) ) < 1' % vm1)
    rb = D(w, A4, 'mpbid', [rlt, D(w, A4, 'absltd', [D(w, A4, 'recld', [vm1c4], '( Re ` %s ) e. RR' % vm1), cst(w, A4, '1re', '1 e. RR')], '( ( abs ` ( Re ` %s ) ) < 1 <-> ( -u 1 < ( Re ` %s ) /\\ ( Re ` %s ) < 1 ) )' % (vm1, vm1, vm1))],
           '( -u 1 < ( Re ` %s ) /\\ ( Re ` %s ) < 1 )' % (vm1, vm1))
    ilt = D(w, A4, 'lelttrd', [D(w, A4, 'abscld', [D(w, A4, 'recnd', [D(w, A4, 'imcld', [vm1c4], '( Im ` %s ) e. RR' % vm1)], '( Im ` %s ) e. CC' % vm1)], '( abs ` ( Im ` %s ) ) e. RR' % vm1),
                               L4(av1r, '%s e. RR' % av1), cst(w, A4, '1re', '1 e. RR'), D(w, A4, 'syl', [vm1c4, w.inst('absimle')], '( abs ` ( Im ` %s ) ) <_ %s' % (vm1, av1)), d2],
            '( abs ` ( Im ` %s ) ) < 1' % vm1)
    ib = D(w, A4, 'mpbid', [ilt, D(w, A4, 'absltd', [D(w, A4, 'imcld', [vm1c4], '( Im ` %s ) e. RR' % vm1), cst(w, A4, '1re', '1 e. RR')], '( ( abs ` ( Im ` %s ) ) < 1 <-> ( -u 1 < ( Im ` %s ) /\\ ( Im ` %s ) < 1 ) )' % (vm1, vm1, vm1))],
           '( -u 1 < ( Im ` %s ) /\\ ( Im ` %s ) < 1 )' % (vm1, vm1))
    rv4 = D(w, A4, 'recld', [vc4], '( Re ` v ) e. RR'); iv4 = D(w, A4, 'imcld', [vc4], '( Im ` v ) e. RR')
    cl6 = Closure(w, A4, {'( Re ` v )': ('RR', rv4), '( Im ` v )': ('RR', iv4)})
    rlo = D(w, A4, 'breqtrd', [D(w, A4, 'simpld', [rb], '-u 1 < ( Re ` %s )' % vm1), rsub], '-u 1 < ( ( Re ` v ) - 1 )')
    rhi = D(w, A4, 'eqbrtrrd', [rsub, D(w, A4, 'simprd', [rb], '( Re ` %s ) < 1' % vm1)], '( ( Re ` v ) - 1 ) < 1')
    ilo = D(w, A4, 'breqtrd', [D(w, A4, 'simpld', [ib], '-u 1 < ( Im ` %s )' % vm1), isub], '-u 1 < ( Im ` v )')
    ihi = D(w, A4, 'eqbrtrrd', [isub, D(w, A4, 'simprd', [ib], '( Im ` %s ) < 1' % vm1)], '( Im ` v ) < 1')
    rin = D(w, A4, 'eleqtrrd', [D(w, A4, 'mpbir3and', [D(w, A4, 'syl2anc', [cst(w, A4, '0re', '0 e. RR'), cst(w, A4, '2re', '2 e. RR'), w.inst('elicc2')],
                                                                         '( ( Re ` v ) e. ( 0 [,] 2 ) <-> ( ( Re ` v ) e. RR /\\ 0 <_ ( Re ` v ) /\\ ( Re ` v ) <_ 2 ) )'),
                                                          rv4, linarith(w, A4, [rlo], '0 <_ ( Re ` v )', closure=cl6), linarith(w, A4, [rhi], '( Re ` v ) <_ 2', closure=cl6)], '( Re ` v ) e. ( 0 [,] 2 )'),
                                D(w, A4, 'oveq12d', [_lift(w, R['ra'], A4), _lift(w, R['rb'], A4)],
                                  '( ( Re ` %s ) [,] ( Re ` %s ) ) = ( 0 [,] 2 )' % (RA, RB))], '( Re ` v ) e. ( ( Re ` %s ) [,] ( Re ` %s ) )' % (RA, RB))
    iin = D(w, A4, 'eleqtrrd', [D(w, A4, 'mpbir3and', [D(w, A4, 'syl2anc', [cst(w, A4, 'neg1rr', '-u 1 e. RR'), cst(w, A4, '1re', '1 e. RR'), w.inst('elicc2')],
                                                                         '( ( Im ` v ) e. ( -u 1 [,] 1 ) <-> ( ( Im ` v ) e. RR /\\ -u 1 <_ ( Im ` v ) /\\ ( Im ` v ) <_ 1 ) )'),
                                                          iv4, linarith(w, A4, [ilo], '-u 1 <_ ( Im ` v )', closure=cl6), linarith(w, A4, [ihi], '( Im ` v ) <_ 1', closure=cl6)], '( Im ` v ) e. ( -u 1 [,] 1 )'),
                                D(w, A4, 'oveq12d', [_lift(w, R['ia'], A4), _lift(w, R['ib'], A4)],
                                  '( ( Im ` %s ) [,] ( Im ` %s ) ) = ( -u 1 [,] 1 )' % (RA, RB))], '( Im ` v ) e. ( ( Im ` %s ) [,] ( Im ` %s ) )' % (RA, RB))
    R4 = {'ac': _lift(w, R['ac'], A4), 'bc': _lift(w, R['bc'], A4)}
    vR = D(w, A4, 'mpbird', [D(w, A4, '3jca', [vc4, rin, iin], '( v e. CC /\\ ( Re ` v ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ ( Im ` v ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) )' % (RA, RB, RA, RB)),
                             rect_mem(w, A4, 'v', R4)], 'v e. %s' % RCT)
    bv = D(w, A4, 'mpd', [L4(L2(bnu, BNu), BNu), D(w, A4, 'syl', [vR, w.s([subu('v')], 'rspcv', '( v e. %s -> ( %s -> %s <_ m ) )' % (RCT, BNu, adq))], '( %s -> %s <_ m )' % (BNu, adq))], '%s <_ m' % adq)
    cl7 = Closure(w, A4, {'m': ('RR', L4(mr2, 'm e. RR')), agv: [('RR', L4(agvr, '%s e. RR' % agv)), ('ge0', L4(agv0, '0 <_ %s' % agv))], ag1: [('RR', L4(ag1r, '%s e. RR' % ag1)), ('ge0', L4(ag10, '0 <_ %s' % ag1))],
                          adq: ('RR', L4(adqr, '%s e. RR' % adq))})
    c2 = linarith(w, A4, [bv, L4(agv0, '0 <_ %s' % agv), L4(ag10, '0 <_ %s' % ag1)], '%s <_ %s' % (adq, T), closure=cl7, atoms=[adq, 'm', agv, ag1])
    cs = w.s([c1, c2, D(w, Av2, 'syl2anc', [cst(w, Av2, '1re', '1 e. RR'), av1r, w.inst('lelttric')], '( 1 <_ %s \\/ %s < 1 )' % (av1, av1))], 'mpjaodan', '( %s -> %s <_ %s )' % (Av2, adq, T))
    BD = lambda c: 'A. v e. %s ( abs ` ( %s ` v ) ) <_ ( %s + ( %s + %s ) )' % (STR, DQ, c, agv, ag1)
    ralb = D(w, Am, 'ralrimiva', [cs], BD('m'))
    csub = w.s([w.s([w.s([w.s([], 'oveq1', '( c = m -> ( c + ( %s + %s ) ) = ( m + ( %s + %s ) ) )' % (agv, ag1, agv, ag1))], 'breq2d',
                          '( c = m -> ( ( abs ` ( %s ` v ) ) <_ ( c + ( %s + %s ) ) <-> ( abs ` ( %s ` v ) ) <_ ( m + ( %s + %s ) ) ) )' % (DQ, agv, ag1, DQ, agv, ag1))], 'ralbidv',
                '( c = m -> ( %s <-> %s ) )' % (BD('c'), BD('m')))], 'rspcev', '( ( m e. RR /\\ %s ) -> E. c e. RR %s )' % (BD('m'), BD('c')))
    exc = D(w, Am, 'mpan' if False else 'syl2anc', [mr, ralb, csub], 'E. c e. RR %s' % BD('c'))
    s1 = w.s([w.s([exc], 'anassrs', '( ( ( %s /\\ m e. RR ) /\\ %s ) -> E. c e. RR %s )' % (A, BNu, BD('c')))], 'ex', '( ( %s /\\ m e. RR ) -> ( %s -> E. c e. RR %s ) )' % (A, BNu, BD('c')))
    part2 = D(w, A, 'mpd', [exm, D(w, A, 'rexlimdva', [s1], '( E. m e. RR %s -> E. c e. RR %s )' % (BNu, BD('c')))], 'E. c e. RR %s' % BD('c'))
    w.qed([D(w, A, 'jca', [part1, part2], Cc)], 'idi', SE['zl3dq'])
    goe(w)


OPL = {'x.': 'holmul', '+': 'zl2hadd', '-': 'zl2hsub', '/': 'holdiv'}


def fvd(w, Ac, bnd, dom, fn, arg, argmem, vstep):
    """( Ac -> ( ( bnd e. dom |-> fn(bnd) ) ` arg ) = fn(arg) ), vstep: ( Ac -> fn(arg) e. _V )"""
    F = '( %s e. %s |-> %s )' % (bnd, dom, fn(bnd))
    if fn(bnd) == fn('QQQ'):
        sub = w.s([], 'eqidd', '( %s = %s -> %s = %s )' % (bnd, arg, fn(bnd), fn(arg)))
    else:
        sub = vsub(w, fn, bnd, arg)
    return w.s([w.s([], 'eqid', '%s = %s' % (F, F)), sub, argmem, vstep], 'fvmptd3', '( %s -> ( %s ` %s ) = %s )' % (Ac, F, arg, fn(arg)))


def vex_closed(lab):
    return lambda w, Ac, f: w.s([w.s([], lab, '%s e. _V' % f)], 'a1i', '( %s -> %s e. _V )' % (Ac, f))


def vex_cc(ccstep):
    return lambda w, Ac, f: D(w, Ac, 'elexd', [ad(w, Ac, ccstep, '%s e. CC' % f)], '%s e. _V' % f)


def comb(w, A, op, ha, fa, hb, fb, Dm, vexa, vexb, nz=None, t='t', s='s'):
    """from HOL ( t |-> fa(t) ) and HOL ( t |-> fb(t) ) on Dm: HOL ( t |-> ( fa(t) op fb(t) ) )"""
    Ma, Mb = '( %s e. %s |-> %s )' % (t, Dm, fa(t)), '( %s e. %s |-> %s )' % (t, Dm, fb(t))
    Zb = lambda q: '( ( %s ` %s ) %s ( %s ` %s ) )' % (Ma, q, op, Mb, q)
    hyps = [ha, hb] + ([nz] if nz else [])
    h = D(w, A, 'syl3anc' if nz else 'syl2anc', hyps + [w.inst(OPL[op])], HOL('( z e. %s |-> %s )' % (Dm, Zb('z')), Dm))
    hs = rebind(w, A, h, Zb, Dm, 'z', s)
    As = '( %s /\\ %s e. %s )' % (A, s, Dm)
    sin = w.s([], 'simpr', '( %s -> %s e. %s )' % (As, s, Dm))
    body = lambda q: '( %s %s %s )' % (fa(q), op, fb(q))
    ev = D(w, As, 'oveq12d', [fvd(w, As, t, Dm, fa, s, sin, vexa(w, As, fa(s))), fvd(w, As, t, Dm, fb, s, sin, vexb(w, As, fb(s)))], '%s = %s' % (Zb(s), body(s)))
    me = D(w, A, 'mpteq2dva', [ev], '( %s e. %s |-> %s ) = ( %s e. %s |-> %s )' % (s, Dm, Zb(s), s, Dm, body(s)))
    hb2 = D(w, A, 'mpbid', [hs, hol_eq(w, A, me, '( %s e. %s |-> %s )' % (s, Dm, Zb(s)), '( %s e. %s |-> %s )' % (s, Dm, body(s)), Dm)], HOL('( %s e. %s |-> %s )' % (s, Dm, body(s)), Dm))
    return rebind(w, A, hb2, body, Dm, s, t), body


def const_hol(w, A, c, cc, Dm, opn, t='t'):
    """HOL ( t e. Dm |-> c ) for a constant c e. CC ( Dm = UO )"""
    h = aff_hol(w, A, '0', c, cst(w, A, '0cn', '0 e. CC'), cc, Dm, opn, new='y')
    fy = lambda q: '( ( 0 x. %s ) + %s )' % (q, c)
    As = '( %s /\\ %s e. %s )' % (A, t, Dm)
    tin = w.s([], 'simpr', '( %s -> %s e. %s )' % (As, t, Dm))
    tc, _, _ = uo_mem(w, As, t, tin)
    ev = D(w, As, 'eqtrd', [D(w, As, 'oveq1d', [D(w, As, 'mul02d', [tc], '( 0 x. %s ) = 0' % t)], '%s = ( 0 + %s )' % (fy(t), c)), D(w, As, 'addlidd', [ad(w, As, cc, '%s e. CC' % c)], '( 0 + %s ) = %s' % (c, c))],
           '%s = %s' % (fy(t), c))
    hy_t = rebind(w, A, h, fy, Dm, 'y', t)
    me = D(w, A, 'mpteq2dva', [ev], '( %s e. %s |-> %s ) = ( %s e. %s |-> %s )' % (t, Dm, fy(t), t, Dm, c))
    return D(w, A, 'mpbid', [hy_t, hol_eq(w, A, me, '( %s e. %s |-> %s )' % (t, Dm, fy(t)), '( %s e. %s |-> %s )' % (t, Dm, c), Dm)], HOL('( %s e. %s |-> %s )' % (t, Dm, c), Dm))


# ---------------------------------------------------------------- zl3fh
if wante('zl3fh', MAIN):
    w = W('zl3fh', 'The closed form ` F ( v ) = ( ( I ( v ) + E J ( 1 - v ) ) g ( v ) - R h ( v ) / 2 ) + R D ( v ) ` is holomorphic on ` U ` for entire ` I ` , ` J ` and holomorphic ` D ` .')
    A, Cc = ante_e('zl3fh')
    hij = D(w, A, 'simp1', [], '( %s /\\ %s )' % (HOL('I', 'CC'), HOL('J', 'CC')))
    hI, hJ = D(w, A, 'simpld', [hij], HOL('I', 'CC')), D(w, A, 'simprd', [hij], HOL('J', 'CC'))
    mer = D(w, A, 'simp2', [], '( %s /\\ ( E e. CC /\\ R e. CC ) )' % LE.MP)
    mp = D(w, A, 'simpld', [mer], LE.MP)
    er_ = D(w, A, 'simprd', [mer], '( E e. CC /\\ R e. CC )')
    ec, rc = D(w, A, 'simpld', [er_], 'E e. CC'), D(w, A, 'simprd', [er_], 'R e. CC')
    hD = D(w, A, 'simp3', [], HOL('D', UO))
    opn = uo_facts(w, A)
    uss = w.s([w.s([], 'cnvimass', '%s C_ dom Re' % UO), w.s([w.s([], 'ref', 'Re : CC --> RR')], 'fdmi', 'dom Re = CC')], 'sseqtri', '%s C_ CC' % UO)
    fI = lambda q: '( I ` %s )' % q
    h1 = rebind(w, A, D(w, A, 'syl2anc', [hI, D(w, A, 'jca', [opn, w.s([uss], 'a1i', '( %s -> %s C_ CC )' % (A, UO))], '( %s e. ( TopOpen ` CCfld ) /\\ %s C_ CC )' % (UO, UO)),
                                           w.inst('zl2hres')], HOL('( z e. %s |-> ( I ` z ) )' % UO, UO)), fI, UO, 'z', 't')
    fDt = lambda q: '( D ` %s )' % q
    hDt = rebind(w, A, D(w, A, 'syl2anc', [hD, D(w, A, 'jca', [opn, cst(w, A, 'ssid', '%s C_ %s' % (UO, UO))], '( %s e. ( TopOpen ` CCfld ) /\\ %s C_ %s )' % (UO, UO, UO)),
                                            w.inst('zl2hres')], HOL('( z e. %s |-> ( D ` z ) )' % UO, UO)), fDt, UO, 'z', 't')
    # J ( 1 - t )
    hA = aff_hol(w, A, '-u 1', '1', cst(w, A, 'neg1cn', '-u 1 e. CC'), cst(w, A, 'ax-1cn', '1 e. CC'), UO, opn, new='y')
    AFm = '( y e. %s |-> ( ( -u 1 x. y ) + 1 ) )' % UO
    Av = '( %s /\\ v e. %s )' % (A, UO)
    vin = w.s([], 'simpr', '( %s -> v e. %s )' % (Av, UO))
    vc, _, _ = uo_mem(w, Av, 'v', vin)
    afv = fv1(w, Av, 'y', UO, lambda q: '( ( -u 1 x. %s ) + 1 )' % q, 'v', vin, 'ovex')
    rng = D(w, A, 'ralrimiva', [D(w, Av, 'eqeltrd', [afv, D(w, Av, 'addcld', [D(w, Av, 'mulcld', [cst(w, Av, 'neg1cn', '-u 1 e. CC'), vc], '( -u 1 x. v ) e. CC'), cst(w, Av, 'ax-1cn', '1 e. CC')],
                                                                         '( ( -u 1 x. v ) + 1 ) e. CC')], '( %s ` v ) e. CC' % AFm)], 'A. v e. %s ( %s ` v ) e. CC' % (UO, AFm))
    hco = D(w, A, 'syl3anc', [hJ, hA, rng, w.inst('zl3hco')], HOL('( z e. %s |-> ( J ` ( %s ` z ) ) )' % (UO, AFm), UO))
    Jb = lambda q: '( J ` ( %s ` %s ) )' % (AFm, q)
    hcs = rebind(w, A, hco, Jb, UO, 'z', 's')
    As = '( %s /\\ s e. %s )' % (A, UO)
    sin = w.s([], 'simpr', '( %s -> s e. %s )' % (As, UO))
    sc, _, _ = uo_mem(w, As, 's', sin)
    ev = D(w, As, 'fveq2d', [D(w, As, 'eqtrd', [fv1(w, As, 'y', UO, lambda q: '( ( -u 1 x. %s ) + 1 )' % q, 's', sin, 'ovex'),
                                                 D(w, As, 'eqtrd', [D(w, As, 'oveq1d', [D(w, As, 'syl', [sc, w.inst('mulm1')], '( -u 1 x. s ) = -u s')], '( ( -u 1 x. s ) + 1 ) = ( -u s + 1 )'),
                                                                    D(w, As, 'eqtrd', [D(w, As, 'addcomd', [D(w, As, 'negcld', [sc], '-u s e. CC'), cst(w, As, 'ax-1cn', '1 e. CC')], '( -u s + 1 ) = ( 1 + -u s )'),
                                                                                       D(w, As, 'negsubd', [cst(w, As, 'ax-1cn', '1 e. CC'), sc], '( 1 + -u s ) = ( 1 - s )')], '( -u s + 1 ) = ( 1 - s )')],
                                                   '( ( -u 1 x. s ) + 1 ) = ( 1 - s )')], '( %s ` s ) = ( 1 - s )' % AFm)], '%s = ( J ` ( 1 - s ) )' % Jb('s'))
    me = D(w, A, 'mpteq2dva', [ev], '( s e. %s |-> %s ) = ( s e. %s |-> ( J ` ( 1 - s ) ) )' % (UO, Jb('s'), UO))
    fJ = lambda q: '( J ` ( 1 - %s ) )' % q
    h2s = D(w, A, 'mpbid', [hcs, hol_eq(w, A, me, '( s e. %s |-> %s )' % (UO, Jb('s')), '( s e. %s |-> %s )' % (UO, fJ('s')), UO)], HOL('( s e. %s |-> %s )' % (UO, fJ('s')), UO))
    h2 = rebind(w, A, h2s, fJ, UO, 's', 't')
    hE = const_hol(w, A, 'E', ec, UO, opn)
    hR = const_hol(w, A, 'R', rc, UO, opn)
    h2c = const_hol(w, A, '2', cst(w, A, '2cn', '2 e. CC'), UO, opn)
    ghl = D(w, A, 'syl', [mp, w.inst('zl3ghl')], L.split_imp(SE['zl3ghl'])[1])
    hH = rebind(w, A, D(w, A, 'simpld', [ghl], HOL('( x e. %s |-> %s )' % (UO, LE.HV('x')), UO)), LE.HV, UO, 'x', 't')
    hG = rebind(w, A, D(w, A, 'simprd', [ghl], HOL('( x e. %s |-> %s )' % (UO, LE.GV('x')), UO)), LE.GV, UO, 'x', 't')
    OV, FV = vex_closed('ovex'), vex_closed('fvex')
    kE, kR, k2 = (lambda q: 'E'), (lambda q: 'R'), (lambda q: '2')
    h3, f3 = comb(w, A, 'x.', hE, kE, h2, fJ, UO, vex_cc(ec), FV)
    h4, f4 = comb(w, A, '+', h1, fI, h3, f3, UO, FV, OV)
    h5, f5 = comb(w, A, 'x.', h4, f4, hG, LE.GV, UO, OV, OV)
    nz = D(w, A, 'ralrimiva', [D(w, Av, 'eqnetrd', [fvd(w, Av, 't', UO, k2, 'v', vin, vex_cc(cst(w, A, '2cn', '2 e. CC'))(w, Av, '2')), cst(w, Av, '2ne0', '2 =/= 0')],
                                 '( ( t e. %s |-> 2 ) ` v ) =/= 0' % UO)], 'A. v e. %s ( ( t e. %s |-> 2 ) ` v ) =/= 0' % (UO, UO))
    h6, f6 = comb(w, A, '/', hH, LE.HV, h2c, k2, UO, OV, vex_cc(cst(w, A, '2cn', '2 e. CC')), nz=nz)
    h7, f7 = comb(w, A, 'x.', hR, kR, h6, f6, UO, vex_cc(rc), OV)
    h8, f8 = comb(w, A, '-', h5, f5, h7, f7, UO, OV, OV)
    h9, f9 = comb(w, A, 'x.', hR, kR, hDt, fDt, UO, vex_cc(rc), FV)
    h10, f10 = comb(w, A, '+', h8, f8, h9, f9, UO, OV, OV)
    fin = rebind(w, A, h10, f10, UO, 't', 'v')
    assert '( v e. %s |-> %s )' % (UO, f10('v')) == LE.FG(), (f10('v'), LE.FG())
    w.qed([fin], 'idi', SE['zl3fh'])
    goe(w)
