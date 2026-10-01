"""Sortie C3 section 3: the open half-plane ( Re ` z ) > T."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c3_lib import *

H = HP()

# ---- elhp ------------------------------------------------------------------
w = W('elhp', 'Membership in the open half-plane, written as a preimage of the real part.')
s1 = w.s([], 'ref', 'Re : CC --> RR')
s3 = w.s([s1, w.inst('ffn')], 'ax-mp', 'Re Fn CC')
w.qed([s3, w.inst('elpreima')], 'ax-mp', '( Z e. %s <-> ( Z e. CC /\\ ( Re ` Z ) e. %s ) )' % (H, IOOT)); run3(w)

# ---- hpss ------------------------------------------------------------------
w = W('hpss', 'The open half-plane is a set of complex numbers.')
s1 = w.s([], 'ref', 'Re : CC --> RR')
s3 = w.s([s1, w.inst('fdm')], 'ax-mp', 'dom Re = CC')
s4 = w.s([], 'cnvimass', '%s C_ dom Re' % H)
w.qed([s4, s3], 'sseqtri', '%s C_ CC' % H); run3(w)

# ---- elhp2 -----------------------------------------------------------------
w = W('elhp2', 'Membership in the open half-plane by the inequality on the real part.')
A0 = 'T e. RR'
tx = w.s([w.s([], 'id', '( %s -> %s )' % (A0, A0))], 'rexrd', '( %s -> T e. RR* )' % A0)
bi = w.s([tx, w.inst('elioopnf')], 'syl', '( %s -> ( ( Re ` Z ) e. %s <-> ( ( Re ` Z ) e. RR /\\ T < ( Re ` Z ) ) ) )' % (A0, IOOT))
# under the extra hypothesis Z e. CC the closure ( Re ` Z ) e. RR is automatic
A1 = '( %s /\\ Z e. CC )' % A0
zc = w.s([], 'simpr', '( %s -> Z e. CC )' % A1)
rz = w.s([zc, w.inst('recl')], 'syl', '( %s -> ( Re ` Z ) e. RR )' % A1)
bi1 = w.s([bi], 'adantr', '( %s -> ( ( Re ` Z ) e. %s <-> ( ( Re ` Z ) e. RR /\\ T < ( Re ` Z ) ) ) )' % (A1, IOOT))
bi2 = w.s([rz], 'biantrurd', '( %s -> ( T < ( Re ` Z ) <-> ( ( Re ` Z ) e. RR /\\ T < ( Re ` Z ) ) ) )' % A1)
eq = w.s([bi1, bi2], 'bitr4d', '( %s -> ( ( Re ` Z ) e. %s <-> T < ( Re ` Z ) ) )' % (A1, IOOT))
pm = w.s([eq], 'pm5.32da', '( %s -> ( ( Z e. CC /\\ ( Re ` Z ) e. %s ) <-> ( Z e. CC /\\ T < ( Re ` Z ) ) ) )' % (A0, IOOT))
el = w.s([w.s([], 'elhp', '( Z e. %s <-> ( Z e. CC /\\ ( Re ` Z ) e. %s ) )' % (H, IOOT))], 'a1i',
         '( %s -> ( Z e. %s <-> ( Z e. CC /\\ ( Re ` Z ) e. %s ) ) )' % (A0, H, IOOT))
w.qed([el, pm], 'bitrd', '( %s -> ( Z e. %s <-> ( Z e. CC /\\ T < ( Re ` Z ) ) ) )' % (A0, H)); run3(w)

# ---- hpopn -----------------------------------------------------------------
w = W('hpopn', 'The open half-plane is an open set of the complex plane.')
ej = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
kk = w.s([], 'cnrestid', '( %s |`t CC ) = %s' % (TOP, TOP))
kr = w.s([kk], 'eqcomi', '%s = ( %s |`t CC )' % (TOP, TOP))
lr = w.s([], 'tgioo4', '%s = ( %s |`t RR )' % (RETOP, TOP))
ccss = w.s([], 'ssid', 'CC C_ CC')
rss = w.s([], 'ax-resscn', 'RR C_ CC')
ce = w.s([ej, kr, lr], 'cncfcn', '( ( CC C_ CC /\\ RR C_ CC ) -> ( CC -cn-> RR ) = ( %s Cn %s ) )' % (TOP, RETOP))
ce2 = w.s([ccss, rss, ce], 'mp2an', '( CC -cn-> RR ) = ( %s Cn %s )' % (TOP, RETOP))
re1 = w.s([], 'recncf', 'Re e. ( CC -cn-> RR )')
re2 = w.s([re1, ce2], 'eleqtri', 'Re e. ( %s Cn %s )' % (TOP, RETOP))
io = w.s([], 'iooretop', '%s e. %s' % (IOOT, RETOP))
w.qed([re2, io, w.inst('cnima')], 'mp2an', '%s e. %s' % (H, TOP)); run3(w)
