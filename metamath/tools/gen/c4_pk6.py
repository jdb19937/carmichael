"""C4, Perron block 6: the kernel line integral, its closure and its crude bound."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from c4_lib import *

DOM = '( CC \\ { 0 } )'
PK0 = PKF('U')
LO = CPT('C', '-u T'); HI = CPT('C', 'T')
A0 = '( U e. RR+ /\\ C e. RR+ /\\ T e. RR+ )'


def ctx(w, A0):
    d = {}
    d['urp'] = w.s([], 'simp1', '( %s -> U e. RR+ )' % A0)
    d['crp'] = w.s([], 'simp2', '( %s -> C e. RR+ )' % A0)
    d['trp'] = w.s([], 'simp3', '( %s -> T e. RR+ )' % A0)
    d['cr'] = w.s([d['crp']], 'rpred', '( %s -> C e. RR )' % A0)
    d['cne'] = w.s([d['crp']], 'rpne0d', '( %s -> C =/= 0 )' % A0)
    d['tr'] = w.s([d['trp']], 'rpred', '( %s -> T e. RR )' % A0)
    d['ntr'] = w.s([d['tr']], 'renegcld', '( %s -> -u T e. RR )' % A0)
    d['cc'] = w.s([d['cr']], 'recnd', '( %s -> C e. CC )' % A0)
    d['tc'] = w.s([d['tr']], 'recnd', '( %s -> T e. CC )' % A0)
    d['ntc'] = w.s([d['ntr']], 'recnd', '( %s -> -u T e. CC )' % A0)
    d['ic'] = w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % A0)
    d['lo'] = w.s([d['cc'], w.s([d['ic'], d['ntc']], 'mulcld', '( %s -> ( _i x. -u T ) e. CC )' % A0)], 'addcld',
                  '( %s -> %s e. CC )' % (A0, LO))
    d['hi'] = w.s([d['cc'], w.s([d['ic'], d['tc']], 'mulcld', '( %s -> ( _i x. T ) e. CC )' % A0)], 'addcld',
                  '( %s -> %s e. CC )' % (A0, HI))
    d['pre'] = w.s([w.s([d['cr'], d['cne']], 'jca', '( %s -> ( C e. RR /\\ C =/= 0 ) )' % A0),
                    w.s([d['ntr'], d['tr']], 'jca', '( %s -> ( -u T e. RR /\\ T e. RR ) )' % A0)], 'jca',
                   '( %s -> ( ( C e. RR /\\ C =/= 0 ) /\\ ( -u T e. RR /\\ T e. RR ) ) )' % A0)
    d['ne0'] = w.s([w.s([d['pre'], w.inst('csegne0')], 'syl',
                        '( %s -> A. u e. ( %s cseg %s ) u e. %s )' % (A0, LO, HI, DOM)),
                    w.s([w.s([], 'dfss3', '( ( %s cseg %s ) C_ %s <-> A. u e. ( %s cseg %s ) u e. %s )' % (LO, HI, DOM, LO, HI, DOM))],
                        'a1i', '( %s -> ( ( %s cseg %s ) C_ %s <-> A. u e. ( %s cseg %s ) u e. %s ) )' % (A0, LO, HI, DOM, LO, HI, DOM))],
                   'mpbird', '( %s -> ( %s cseg %s ) C_ %s )' % (A0, LO, HI, DOM))
    d['fcn'] = w.s([w.s([d['urp'], w.s([w.s([], 'ssid', '%s C_ %s' % (DOM, DOM))], 'a1i', '( %s -> %s C_ %s )' % (A0, DOM, DOM))],
                        'jca', '( %s -> ( U e. RR+ /\\ %s C_ %s ) )' % (A0, DOM, DOM)), w.inst('pkfcn')], 'syl',
                   '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, PK0, DOM))
    return d


# ---------------------------------------------------------------- pkcl
w = W('pkcl', 'The truncated Perron kernel line integral is a complex number: the '
      'segment from ` C - _i T ` to ` C + _i T ` misses the origin ( ~ csegne0 ) and '
      'the integrand is continuous there ( ~ pkfcn ).')
d = ctx(w, A0)
w.qed([w.s([d['lo'], d['hi']], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, LO, HI)),
       w.s([d['fcn'], d['ne0']], 'jca',
           '( %s -> ( %s e. ( %s -cn-> CC ) /\\ ( %s cseg %s ) C_ %s ) )' % (A0, PK0, DOM, LO, HI, DOM)),
       w.inst('lintcl')], 'syl2anc', '( %s -> ( %s lint <. %s , %s >. ) e. CC )' % (A0, PK0, LO, HI))
run4(w)

# ---------------------------------------------------------------- pkbnd0
w = W('pkbnd0', 'The crude bound on the truncated Perron kernel line integral: the '
      'modulus of the integrand is at most ` ( U ^c C ) / C ` on the whole segment '
      'and the segment has length ` 2 T ` ( ~ vedgbnd ).')
d = ctx(w, A0)
vb = w.s([w.s([w.s([d['urp'], w.s([d['cr'], d['cne']], 'jca', '( %s -> ( C e. RR /\\ C =/= 0 ) )' % A0)], 'jca',
                   '( %s -> ( U e. RR+ /\\ ( C e. RR /\\ C =/= 0 ) ) )' % A0),
               w.s([d['ntr'], d['tr']], 'jca', '( %s -> ( -u T e. RR /\\ T e. RR ) )' % A0)], 'jca',
              '( %s -> ( ( U e. RR+ /\\ ( C e. RR /\\ C =/= 0 ) ) /\\ ( -u T e. RR /\\ T e. RR ) ) )' % A0),
          w.inst('vedgbnd')], 'syl',
         '( %s -> ( abs ` ( %s lint <. %s , %s >. ) ) <_ ( ( ( U ^c C ) / ( abs ` C ) ) x. ( abs ` ( %s - %s ) ) ) )' % (A0, PK0, LO, HI, HI, LO))
absc = w.s([d['cr'], w.s([d['crp']], 'rpge0d', '( %s -> 0 <_ C )' % A0)], 'absidd', '( %s -> ( abs ` C ) = C )' % A0)
# ( HI - LO ) = ( _i x. ( 2 x. T ) )
sub = w.s([d['cc'], w.s([d['ic'], d['tc']], 'mulcld', '( %s -> ( _i x. T ) e. CC )' % A0), d['cc'],
           w.s([d['ic'], d['ntc']], 'mulcld', '( %s -> ( _i x. -u T ) e. CC )' % A0)], 'addsub4d',
          '( %s -> ( %s - %s ) = ( ( C - C ) + ( ( _i x. T ) - ( _i x. -u T ) ) ) )' % (A0, HI, LO))
s0 = w.s([d['cc']], 'subidd', '( %s -> ( C - C ) = 0 )' % A0)
sd = w.s([d['ic'], d['tc'], d['ntc']], 'subdid',
         '( %s -> ( _i x. ( T - -u T ) ) = ( ( _i x. T ) - ( _i x. -u T ) ) )' % A0)
tt = w.s([d['tc']], 'subnegd', '( %s -> ( T - -u T ) = ( T + T ) )' % A0)
t2 = w.s([d['tc']], '2timesd', '( %s -> ( 2 x. T ) = ( T + T ) )' % A0)
ttv = w.s([tt, w.s([t2], 'eqcomd', '( %s -> ( T + T ) = ( 2 x. T ) )' % A0)], 'eqtrd',
          '( %s -> ( T - -u T ) = ( 2 x. T ) )' % A0)
sd2 = w.s([w.s([w.s([ttv], 'oveq2d', '( %s -> ( _i x. ( T - -u T ) ) = ( _i x. ( 2 x. T ) ) )' % A0)], 'eqcomd',
               '( %s -> ( _i x. ( 2 x. T ) ) = ( _i x. ( T - -u T ) ) )' % A0), sd], 'eqtrd',
          '( %s -> ( _i x. ( 2 x. T ) ) = ( ( _i x. T ) - ( _i x. -u T ) ) )' % A0)
sub2 = w.s([sub, w.s([s0, w.s([sd2], 'eqcomd', '( %s -> ( ( _i x. T ) - ( _i x. -u T ) ) = ( _i x. ( 2 x. T ) ) )' % A0)],
                     'oveq12d', '( %s -> ( ( C - C ) + ( ( _i x. T ) - ( _i x. -u T ) ) ) = ( 0 + ( _i x. ( 2 x. T ) ) ) )' % A0)],
           'eqtrd', '( %s -> ( %s - %s ) = ( 0 + ( _i x. ( 2 x. T ) ) ) )' % (A0, HI, LO))
t2c = w.s([w.s([w.s([], '2cn', '2 e. CC')], 'a1i', '( %s -> 2 e. CC )' % A0), d['tc']], 'mulcld',
          '( %s -> ( 2 x. T ) e. CC )' % A0)
sub3 = w.s([sub2, w.s([w.s([d['ic'], t2c], 'mulcld', '( %s -> ( _i x. ( 2 x. T ) ) e. CC )' % A0)], 'addlidd',
                      '( %s -> ( 0 + ( _i x. ( 2 x. T ) ) ) = ( _i x. ( 2 x. T ) ) )' % A0)], 'eqtrd',
           '( %s -> ( %s - %s ) = ( _i x. ( 2 x. T ) ) )' % (A0, HI, LO))
absi = w.s([w.s([w.s([sub3], 'fveq2d', '( %s -> ( abs ` ( %s - %s ) ) = ( abs ` ( _i x. ( 2 x. T ) ) ) )' % (A0, HI, LO)),
                 w.s([d['ic'], t2c], 'absmuld', '( %s -> ( abs ` ( _i x. ( 2 x. T ) ) ) = ( ( abs ` _i ) x. ( abs ` ( 2 x. T ) ) )' % A0 + ' )')],
                'eqtrd', '( %s -> ( abs ` ( %s - %s ) ) = ( ( abs ` _i ) x. ( abs ` ( 2 x. T ) ) ) )' % (A0, HI, LO))], 'id',
            '( %s -> ( abs ` ( %s - %s ) ) = ( ( abs ` _i ) x. ( abs ` ( 2 x. T ) ) ) )' % (A0, HI, LO))
w.lines.pop()
absi = w.s([w.s([sub3], 'fveq2d', '( %s -> ( abs ` ( %s - %s ) ) = ( abs ` ( _i x. ( 2 x. T ) ) ) )' % (A0, HI, LO)),
            w.s([d['ic'], t2c], 'absmuld',
                '( %s -> ( abs ` ( _i x. ( 2 x. T ) ) ) = ( ( abs ` _i ) x. ( abs ` ( 2 x. T ) ) ) )' % A0)],
           'eqtrd', '( %s -> ( abs ` ( %s - %s ) ) = ( ( abs ` _i ) x. ( abs ` ( 2 x. T ) ) ) )' % (A0, HI, LO))
t2rp = w.s([w.s([w.s([], '2rp', '2 e. RR+')], 'a1i', '( %s -> 2 e. RR+ )' % A0), d['trp']], 'rpmulcld',
           '( %s -> ( 2 x. T ) e. RR+ )' % A0)
abs2 = w.s([w.s([t2rp], 'rpred', '( %s -> ( 2 x. T ) e. RR )' % A0),
            w.s([t2rp], 'rpge0d', '( %s -> 0 <_ ( 2 x. T ) )' % A0)], 'absidd',
           '( %s -> ( abs ` ( 2 x. T ) ) = ( 2 x. T ) )' % A0)
absi2 = w.s([absi, w.s([w.s([w.s([], 'absi', '( abs ` _i ) = 1')], 'a1i', '( %s -> ( abs ` _i ) = 1 )' % A0), abs2],
                       'oveq12d', '( %s -> ( ( abs ` _i ) x. ( abs ` ( 2 x. T ) ) ) = ( 1 x. ( 2 x. T ) ) )' % A0)],
            'eqtrd', '( %s -> ( abs ` ( %s - %s ) ) = ( 1 x. ( 2 x. T ) ) )' % (A0, HI, LO))
absi3 = w.s([absi2, w.s([t2c], 'mullidd', '( %s -> ( 1 x. ( 2 x. T ) ) = ( 2 x. T ) )' % A0)], 'eqtrd',
            '( %s -> ( abs ` ( %s - %s ) ) = ( 2 x. T ) )' % (A0, HI, LO))
absc2 = w.s([absc], 'oveq2d', '( %s -> ( ( U ^c C ) / ( abs ` C ) ) = ( ( U ^c C ) / C ) )' % A0)
w.qed([vb, w.s([absc2, absi3], 'oveq12d',
               '( %s -> ( ( ( U ^c C ) / ( abs ` C ) ) x. ( abs ` ( %s - %s ) ) ) = ( ( ( U ^c C ) / C ) x. ( 2 x. T ) ) )' % (A0, HI, LO))],
      'breqtrd', '( %s -> ( abs ` ( %s lint <. %s , %s >. ) ) <_ ( ( ( U ^c C ) / C ) x. ( 2 x. T ) ) )' % (A0, PK0, LO, HI))
run4(w)
