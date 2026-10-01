"""Sortie KD1: zeros of L in the 13/8 square have real part at most 1 (kdre1)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from kd1lib import *
from cl import formula_of, lift, split_imp
from c9lib import top_and

only = sys.argv[1:]


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


def gen_re1():
    w = W('kdre1', 'Lean ` KDerivDetect.re_lt_one_of_mem_zeroDiskFinset ` , weak form: a zero ` Q ` of ` L ( s , chi ) ` in the ` 13 / 8 ` square has ` Re Q <_ 1 ` (non-vanishing on ` Re > 1 ` ; the campaign has no non-vanishing on ` Re = 1 ` , and every consumer needs only ` <_ ` ).')
    A0 = S['kdre1'].split(' -> ( Re ` Q )')[0][2:]
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    chi = s([], 'simp1', CHI); tr = s([], 'simp2', 'T e. RR'); qz = s([], 'simp3', 'Q e. %s' % ZD())
    SQ13 = SQ(CT('T'), R138)
    ely = w.s([w.s([], 'fveqeq2', '( r = Q -> ( ( %s ` r ) = 0 <-> ( %s ` Q ) = 0 ) )' % (LFN, LFN))], 'elrab', '( Q e. %s <-> ( Q e. %s /\\ ( %s ` Q ) = 0 ) )' % (ZD(), SQ13, LFN))
    qq = s([qz, ely], 'sylib', '( Q e. %s /\\ ( %s ` Q ) = 0 )' % (SQ13, LFN))
    qs = s([qq], 'simpld', 'Q e. %s' % SQ13); l0 = s([qq], 'simprd', '( %s ` Q ) = 0' % LFN)
    from kd1_q import corners
    c = Closure(w, A0, {'T': ('RR', tr)})
    cct = s([w.s([w.s([], '2cn', '2 e. CC')], 'a1i', '( %s -> 2 e. CC )' % A0), s([w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % A0), s([tr], 'recnd', 'T e. CC')], 'mulcld', '( _i x. T ) e. CC')],
            'addcld', '%s e. CC' % CT('T'))
    rc = s([w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % A0), tr, w.inst('crre')], 'syl2anc', '( Re ` %s ) = 2' % CT('T'))
    ic = s([w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % A0), tr, w.inst('crim')], 'syl2anc', '( Im ` %s ) = T' % CT('T'))
    K = corners(w, A0, CT('T'), R138, cct, rc, ic, c.mem(R138, 'RR'))
    c.leaf('( Re ` %s )' % A13, 'RR', s([K['lo']], 'recld', '( Re ` %s ) e. RR' % A13)); c.atom('( Re ` %s )' % A13)
    ra0 = __import__('lin').linarith(w, A0, [K['ReA']], '0 < ( Re ` %s )' % A13, closure=c)
    rhp = s([s([K['lo'], K['hi']], 'jca', '( %s e. CC /\\ %s e. CC )' % (A13, B13)), ra0, w.inst('ef2rhp')], 'syl2anc', '( %s C_ %s /\\ %s C_ ( CC \\ { 0 } ) )' % (SQ13, HP0, SQ13))
    qh = s([s([rhp], 'simpld', '%s C_ %s' % (SQ13, HP0)), qs], 'sseldd', 'Q e. %s' % HP0)
    DDs = stmt('ef2ddl').split(' -> ', 1)[1][:-2]
    dd = s([chi, w.inst('ef2ddl')], 'syl', DDs)
    NV = top_and(top_and(DDs)[2])[1]
    nv = s([s([dd], 'simp3d', top_and(DDs)[2])], 'simprd', NV)
    idw = w.s([], 'id', '( w = Q -> w = Q )')
    cw, nw = w.wcongr('( 1 < ( Re ` w ) -> ( %s ` w ) =/= 0 )' % LFN, {'w': 'Q'}, 'w = Q', {'w': idw})
    iq = s([qh, nv, w.s([cw], 'rspcv', '( Q e. %s -> ( %s -> %s ) )' % (HP0, NV, nw))], 'sylc', nw)
    n1 = s([iq, s([l0, w.s([], 'nne', '( -. ( %s ` Q ) =/= 0 <-> ( %s ` Q ) = 0 )' % (LFN, LFN))], 'sylibr', '-. ( %s ` Q ) =/= 0' % LFN)], 'mtod', '-. 1 < ( Re ` Q )')
    qc = s([s([s([K['lo'], K['hi']], 'jca', '( %s e. CC /\\ %s e. CC )' % (A13, B13)), w.inst('crectss')], 'syl', '%s C_ CC' % SQ13), qs], 'sseldd', 'Q e. CC')
    w.qed([s([qc], 'recld', '( Re ` Q ) e. RR'), w.s([], '1red', '( %s -> 1 e. RR )' % A0), n1], 'lenltd' if False else 'T.', S['kdre1']) if False else None
    fin = s([s([s([qc], 'recld', '( Re ` Q ) e. RR'), w.s([], '1red', '( %s -> 1 e. RR )' % A0)], 'lenltd', '( ( Re ` Q ) <_ 1 <-> -. 1 < ( Re ` Q ) )'), n1], 'mpbird', '( Re ` Q ) <_ 1')
    w.lines.append('qed:%s:idi |- %s' % (fin, S['kdre1']))
    return run(w)


if __name__ == '__main__':
    gen_re1()
