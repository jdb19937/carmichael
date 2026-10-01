"""Sortie C2 section 3.1: holomorphy on an open domain."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c2_lib import *

DVF = '( CC _D F )'

# ---- holdm -----------------------------------------------------------------
w = W('holdm', 'The domain of the derivative of a function holomorphic on its whole domain is that domain.')
A0 = HOL
fcn = w.s([], 'simpl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
dd = w.s([], 'simpr', '( %s -> D C_ dom %s )' % (A0, DVF))
dcc = w.s([fcn, w.inst('cncfrss')], 'syl', '( %s -> D C_ CC )' % A0)
ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)
cid = w.s([w.s([], 'ssid', 'CC C_ CC')], 'a1i', '( %s -> CC C_ CC )' % A0)
bs = w.s([cid, ff, dcc], 'dvbss', '( %s -> dom %s C_ D )' % (A0, DVF))
w.qed([bs, dd], 'eqssd', '( %s -> dom %s = D )' % (A0, DVF)); run1(w)

# ---- holf ------------------------------------------------------------------
w = W('holf', 'The derivative of a function holomorphic on its whole domain is a function on that domain.')
A0 = HOL
dm = w.s([w.inst('holdm')], 'ax-mp', '( %s -> dom %s = D )' % (A0, DVF), name='d1') if False else w.s([], 'holdm', '( %s -> dom %s = D )' % (A0, DVF))
df = w.s([w.s([], 'dvfcn', '%s : dom %s --> CC' % (DVF, DVF))], 'a1i', '( %s -> %s : dom %s --> CC )' % (A0, DVF, DVF))
w.qed([df, w.s([dm], 'feq2d', '( %s -> ( %s : dom %s --> CC <-> %s : D --> CC ) )' % (A0, DVF, DVF, DVF))],
      'mpbid', '( %s -> %s : D --> CC )' % (A0, DVF)); run1(w)

# ---- holdv -----------------------------------------------------------------
w = W('holdv', 'The derivative of a function holomorphic on its whole domain, as a mapping: the input every mapping-form derivative rule needs.')
A0 = HOL
fcn = w.s([], 'simpl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)
fm = w.s([ff], 'feqmptd', '( %s -> F = %s )' % (A0, MP('z', 'D', '( F ` z )')))
dvm = w.s([w.s([], 'holf', '( %s -> %s : D --> CC )' % (A0, DVF))], 'feqmptd',
          '( %s -> %s = %s )' % (A0, DVF, MP('z', 'D', '( %s ` z )' % DVF)))
e1 = w.s([fm], 'oveq2d', '( %s -> %s = ( CC _D %s ) )' % (A0, DVF, MP('z', 'D', '( F ` z )')))
w.qed([w.s([e1], 'eqcomd', '( %s -> ( CC _D %s ) = %s )' % (A0, MP('z', 'D', '( F ` z )'), DVF)), dvm],
      'eqtrd', '( %s -> ( CC _D %s ) = %s )' % (A0, MP('z', 'D', '( F ` z )'), MP('z', 'D', '( %s ` z )' % DVF))); run1(w)

# ---- holopn ----------------------------------------------------------------
w = W('holopn', 'The domain of a function holomorphic on its whole domain is open.')
A0 = HOL
fcn = w.s([], 'simpl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
dd = w.s([], 'simpr', '( %s -> D C_ dom %s )' % (A0, DVF))
dcc = w.s([fcn, w.inst('cncfrss')], 'syl', '( %s -> D C_ CC )' % A0)
ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)
cid = w.s([w.s([], 'ssid', 'CC C_ CC')], 'a1i', '( %s -> CC C_ CC )' % A0)
ej = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
jr = w.s([w.s([], 'cnrestid', '( %s |`t CC ) = %s' % (TOP, TOP))], 'eqcomi', '%s = ( %s |`t CC )' % (TOP, TOP))
ntr = w.s([cid, ff, dcc, jr, ej], 'dvbssntr', '( %s -> dom %s C_ ( ( int ` %s ) ` D ) )' % (A0, DVF, TOP))
dint = w.s([dd, ntr], 'sstrd', '( %s -> D C_ ( ( int ` %s ) ` D ) )' % (A0, TOP))
ux = w.s([w.s([], 'unicntop', 'CC = U. %s' % TOP)], 'eqcomi', 'U. %s = CC' % TOP)
uxr = w.s([ux], 'eqcomi', 'CC = U. %s' % TOP)
topt = w.s([w.s([ej], 'cnfldtop', '%s e. Top' % TOP)], 'a1i', '( %s -> %s e. Top )' % (A0, TOP))
n2c = w.s([uxr], 'ntrss2', '( ( %s e. Top /\\ D C_ CC ) -> ( ( int ` %s ) ` D ) C_ D )' % (TOP, TOP))
n2 = w.s([topt, dcc, n2c], 'syl2anc', '( %s -> ( ( int ` %s ) ` D ) C_ D )' % (A0, TOP))
eqd = w.s([n2, dint], 'eqssd', '( %s -> ( ( int ` %s ) ` D ) = D )' % (A0, TOP))
i3c = w.s([uxr], 'isopn3', '( ( %s e. Top /\\ D C_ CC ) -> ( D e. %s <-> ( ( int ` %s ) ` D ) = D ) )' % (TOP, TOP, TOP))
w.qed([eqd, w.s([topt, dcc, i3c], 'syl2anc', '( %s -> ( D e. %s <-> ( ( int ` %s ) ` D ) = D ) )' % (A0, TOP, TOP))],
      'mpbird', '( %s -> D e. %s )' % (A0, TOP)); run1(w)

# ---- holcrect --------------------------------------------------------------
w = W('holcrect', 'Holomorphy on an open domain gives the rectangle form of holomorphy for any rectangle inside it.')
A0 = '( %s /\\ ( A crect B ) C_ D )' % HOL
hl = w.s([], 'simpl', '( %s -> %s )' % (A0, HOL))
rd = w.s([], 'simpr', '( %s -> ( A crect B ) C_ D )' % A0)
fcn = w.s([hl, w.inst('simpl')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
dd = w.s([hl, w.inst('simpr')], 'syl', '( %s -> D C_ dom %s )' % (A0, DVF))
w.qed([fcn, w.s([rd, dd], 'sstrd', '( %s -> ( A crect B ) C_ dom %s )' % (A0, DVF))], 'jca',
      '( %s -> %s )' % (A0, HOLO)); run1(w)
