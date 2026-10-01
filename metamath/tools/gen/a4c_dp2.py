"""Sortie A4c, batch 3b: the accumulator of one dpGo body."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from a4clib import *

only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

NONE = '( inr ` (/) )'
DPO = '( ( L e. NN /\\ P e. NN0 ) /\\ T e. Tbl )'
MOD = '( ( F x. P ) mod L )'
CSW = '( <" P "> ++ ( 2nd ` ( T ` F ) ) )'
ACC = lambda a: 'if ( ( T ` F ) = %s , %s , ( ( %s SetIfNone %s ) ` %s ) )' % (NONE, a, a, MOD, CSW)
SNA = '( ( A SetIfNone %s ) ` %s )' % (MOD, CSW)
A3 = '( %s /\\ ( F e. NN0 /\\ A e. Tbl ) )' % DPO

# ------------------------------------------------------------------ dpgomcl
if not only or 'dpgomcl' in only:
    w = W('dpgomcl', 'The residue the dpGo body writes to is a residue.')
    A = '( ( L e. NN /\\ P e. NN0 ) /\\ F e. NN0 )'
    ll = w.s([w.s([], 'simpl', '( %s -> ( L e. NN /\\ P e. NN0 ) )' % A)], 'simpld', '( %s -> L e. NN )' % A)
    pp = w.s([w.s([], 'simpl', '( %s -> ( L e. NN /\\ P e. NN0 ) )' % A)], 'simprd', '( %s -> P e. NN0 )' % A)
    ff = w.s([], 'simpr', '( %s -> F e. NN0 )' % A)
    mz = w.s([w.s([ff], 'nn0zd', '( %s -> F e. ZZ )' % A), w.s([pp], 'nn0zd', '( %s -> P e. ZZ )' % A)], 'zmulcld',
             '( %s -> ( F x. P ) e. ZZ )' % A)
    w.qed([mz, ll, w.inst('zmodcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (A, MOD))
    run(w)

# ------------------------------------------------------------------ dpgowcl
if not only or 'dpgowcl' in only:
    w = W('dpgowcl', 'The witness list the dpGo body writes is a word.')
    A = '( ( P e. NN0 /\\ T e. Tbl ) /\\ ( F e. NN0 /\\ ( T ` F ) =/= %s ) )' % NONE
    pp = w.s([w.s([], 'simpl', '( %s -> ( P e. NN0 /\\ T e. Tbl ) )' % A)], 'simpld', '( %s -> P e. NN0 )' % A)
    tt = w.s([w.s([], 'simpl', '( %s -> ( P e. NN0 /\\ T e. Tbl ) )' % A)], 'simprd', '( %s -> T e. Tbl )' % A)
    ff = w.s([], 'simprl', '( %s -> F e. NN0 )' % A)
    nn = w.s([], 'simprr', '( %s -> ( T ` F ) =/= %s )' % (A, NONE))
    pay = w.s([w.s([w.s([tt, ff], 'jca', '( %s -> ( T e. Tbl /\\ F e. NN0 ) )' % A), nn], 'jca',
                   '( %s -> ( ( T e. Tbl /\\ F e. NN0 ) /\\ ( T ` F ) =/= %s ) )' % (A, NONE)), w.inst('tblpay')], 'syl',
              '( %s -> ( ( 2nd ` ( T ` F ) ) e. Word NN0 /\\ ( T ` F ) = ( inl ` ( 2nd ` ( T ` F ) ) ) ) )' % A)
    s1c = w.s([pp, w.inst('s1cl')], 'syl', '( %s -> <" P "> e. Word NN0 )' % A)
    w.qed([s1c, w.s([pay], 'simpld', '( %s -> ( 2nd ` ( T ` F ) ) e. Word NN0 )' % A), w.inst('ccatcl')], 'syl2anc',
          '( %s -> %s e. Word NN0 )' % (A, CSW))
    run(w)

def a3ctx(w, A, tag3=None):
    """L e. NN, P e. NN0, T e. Tbl, F e. NN0, A e. Tbl from an antecedent whose
    first conjunct is DPO and second ( F e. NN0 /\\ A e. Tbl ), reached by simpl/simpr"""
    dp = w.s([], 'simp1' if tag3 else 'simpl', '( %s -> %s )' % (A, DPO))
    fa = w.s([], 'simp2' if tag3 else 'simpr', '( %s -> ( F e. NN0 /\\ A e. Tbl ) )' % A)
    ll = w.s([w.s([dp], 'simpld', '( %s -> ( L e. NN /\\ P e. NN0 ) )' % A)], 'simpld', '( %s -> L e. NN )' % A)
    pp = w.s([w.s([dp], 'simpld', '( %s -> ( L e. NN /\\ P e. NN0 ) )' % A)], 'simprd', '( %s -> P e. NN0 )' % A)
    tt = w.s([dp], 'simprd', '( %s -> T e. Tbl )' % A)
    ff = w.s([fa], 'simpld', '( %s -> F e. NN0 )' % A)
    aa = w.s([fa], 'simprd', '( %s -> A e. Tbl )' % A)
    return ll, pp, tt, ff, aa

def sncl(w, A, ll, pp, tt, ff, aa):
    """( A -> MOD e. NN0 ), and under ( T ` F ) =/= NONE the word and the update"""
    mz = w.s([w.s([w.s([ll, pp], 'jca', '( %s -> ( L e. NN /\\ P e. NN0 ) )' % A), ff], 'jca',
                  '( %s -> ( ( L e. NN /\\ P e. NN0 ) /\\ F e. NN0 ) )' % A), w.inst('dpgomcl')], 'syl',
             '( %s -> %s e. NN0 )' % (A, MOD))
    return mz

def wclstep(w, B, pp, tt, ff, nn):
    return w.s([w.s([w.s([pp, tt], 'jca', '( %s -> ( P e. NN0 /\\ T e. Tbl ) )' % B),
                     w.s([ff, nn], 'jca', '( %s -> ( F e. NN0 /\\ ( T ` F ) =/= %s ) )' % (B, NONE))], 'jca',
                    '( %s -> ( ( P e. NN0 /\\ T e. Tbl ) /\\ ( F e. NN0 /\\ ( T ` F ) =/= %s ) ) )' % (B, NONE)),
                w.inst('dpgowcl')], 'syl', '( %s -> %s e. Word NN0 )' % (B, CSW))

# ------------------------------------------------------------------ dpgoace
if not only or 'dpgoace' in only:
    w = W('dpgoace', 'The dpGo body leaves a nonempty entry of the accumulator alone.')
    A = '( %s /\\ ( F e. NN0 /\\ A e. Tbl ) /\\ ( C e. NN0 /\\ ( A ` C ) =/= %s ) )' % (DPO, NONE)
    ll, pp, tt, ff, aa = a3ctx(w, A, True)
    cc = w.s([w.s([], 'simp3', '( %s -> ( C e. NN0 /\\ ( A ` C ) =/= %s ) )' % (A, NONE))], 'simpld',
             '( %s -> C e. NN0 )' % A)
    ac = w.s([w.s([], 'simp3', '( %s -> ( C e. NN0 /\\ ( A ` C ) =/= %s ) )' % (A, NONE))], 'simprd',
             '( %s -> ( A ` C ) =/= %s )' % (A, NONE))
    C1 = '( %s /\\ ( T ` F ) = %s )' % (A, NONE)
    e1 = w.s([w.s([w.s([], 'simpr', '( %s -> ( T ` F ) = %s )' % (C1, NONE))], 'iftrued',
                  '( %s -> %s = A )' % (C1, ACC('A')))], 'fveq1d', '( %s -> ( %s ` C ) = ( A ` C ) )' % (C1, ACC('A')))
    B = '( %s /\\ -. ( T ` F ) = %s )' % (A, NONE)
    nn = w.s([w.s([], 'simpr', '( %s -> -. ( T ` F ) = %s )' % (B, NONE)), w.inst('neqned')], 'syl',
             '( %s -> ( T ` F ) =/= %s )' % (B, NONE))
    ppB = w.s([pp], 'adantr', '( %s -> P e. NN0 )' % B)
    ttB = w.s([tt], 'adantr', '( %s -> T e. Tbl )' % B)
    ffB = w.s([ff], 'adantr', '( %s -> F e. NN0 )' % B)
    aaB = w.s([aa], 'adantr', '( %s -> A e. Tbl )' % B)
    llB = w.s([ll], 'adantr', '( %s -> L e. NN )' % B)
    ccB = w.s([cc], 'adantr', '( %s -> C e. NN0 )' % B)
    acB = w.s([ac], 'adantr', '( %s -> ( A ` C ) =/= %s )' % (B, NONE))
    mz = sncl(w, B, llB, ppB, ttB, ffB, aaB)
    wc = wclstep(w, B, ppB, ttB, ffB, nn)
    pers = w.s([w.s([w.s([aaB, mz, wc], '3jca', '( %s -> ( A e. Tbl /\\ %s e. NN0 /\\ %s e. Word NN0 ) )' % (B, MOD, CSW)),
                     w.s([ccB, acB], 'jca', '( %s -> ( C e. NN0 /\\ ( A ` C ) =/= %s ) )' % (B, NONE))], 'jca',
                    '( %s -> ( ( A e. Tbl /\\ %s e. NN0 /\\ %s e. Word NN0 ) /\\ ( C e. NN0 /\\ ( A ` C ) =/= %s ) ) )' % (B, MOD, CSW, NONE)),
                w.inst('sinpers')], 'syl', '( %s -> ( %s ` C ) = ( A ` C ) )' % (B, SNA))
    e2 = w.s([w.s([w.s([w.s([], 'simpr', '( %s -> -. ( T ` F ) = %s )' % (B, NONE))], 'iffalsed',
                       '( %s -> %s = %s )' % (B, ACC('A'), SNA))], 'fveq1d',
                  '( %s -> ( %s ` C ) = ( %s ` C ) )' % (B, ACC('A'), SNA)), pers], 'eqtrd',
             '( %s -> ( %s ` C ) = ( A ` C ) )' % (B, ACC('A')))
    w.qed([e1, e2], 'pm2.61dan', '( %s -> ( %s ` C ) = ( A ` C ) )' % (A, ACC('A')))
    run(w)

# ------------------------------------------------------------------ dpgoacnn
if not only or 'dpgoacnn' in only:
    w = W('dpgoacnn', 'The dpGo body keeps a nonempty entry of the accumulator nonempty.')
    A = '( %s /\\ ( F e. NN0 /\\ A e. Tbl ) /\\ ( C e. NN0 /\\ ( A ` C ) =/= %s ) )' % (DPO, NONE)
    e = w.s([], 'dpgoace', '( %s -> ( %s ` C ) = ( A ` C ) )' % (A, ACC('A')))
    ac = w.s([w.s([], 'simp3', '( %s -> ( C e. NN0 /\\ ( A ` C ) =/= %s ) )' % (A, NONE))], 'simprd',
             '( %s -> ( A ` C ) =/= %s )' % (A, NONE))
    w.qed([e, ac], 'eqnetrd', '( %s -> ( %s ` C ) =/= %s )' % (A, ACC('A'), NONE))
    run(w)

# ------------------------------------------------------------------ dpgoacself
if not only or 'dpgoacself' in only:
    w = W('dpgoacself', 'The dpGo body fills the residue it writes to.')
    A = '( %s /\\ ( F e. NN0 /\\ A e. Tbl ) /\\ ( T ` F ) =/= %s )' % (DPO, NONE)
    ll, pp, tt, ff, aa = a3ctx(w, A, True)
    nn = w.s([], 'simp3', '( %s -> ( T ` F ) =/= %s )' % (A, NONE))
    mz = sncl(w, A, ll, pp, tt, ff, aa)
    wc = wclstep(w, A, pp, tt, ff, nn)
    slf = w.s([w.s([aa, mz, wc], '3jca', '( %s -> ( A e. Tbl /\\ %s e. NN0 /\\ %s e. Word NN0 ) )' % (A, MOD, CSW)),
               w.inst('sinself')], 'syl', '( %s -> ( %s ` %s ) =/= %s )' % (A, SNA, MOD, NONE))
    ne = w.s([nn, w.inst('neneqd')], 'syl', '( %s -> -. ( T ` F ) = %s )' % (A, NONE))
    w.qed([w.s([w.s([ne], 'iffalsed', '( %s -> %s = %s )' % (A, ACC('A'), SNA))], 'fveq1d',
               '( %s -> ( %s ` %s ) = ( %s ` %s ) )' % (A, ACC('A'), MOD, SNA, MOD)), slf], 'eqnetrd',
          '( %s -> ( %s ` %s ) =/= %s )' % (A, ACC('A'), MOD, NONE))
    run(w)

# ------------------------------------------------------------------ dpgoacc
if not only or 'dpgoacc' in only:
    w = W('dpgoacc', 'Every nonempty entry after a dpGo body is old or the new one.')
    A = '( %s /\\ ( F e. NN0 /\\ A e. Tbl ) /\\ ( C e. NN0 /\\ ( %s ` C ) =/= %s ) )' % (DPO, ACC('A'), NONE)
    CONC = '( ( A ` C ) = ( %s ` C ) \\/ ( ( ( T ` F ) =/= %s /\\ C = %s ) /\\ ( 2nd ` ( %s ` C ) ) = %s ) )' % (ACC('A'), NONE, MOD, ACC('A'), CSW)
    ll, pp, tt, ff, aa = a3ctx(w, A, True)
    cc = w.s([w.s([], 'simp3', '( %s -> ( C e. NN0 /\\ ( %s ` C ) =/= %s ) )' % (A, ACC('A'), NONE))], 'simpld',
             '( %s -> C e. NN0 )' % A)
    ac = w.s([w.s([], 'simp3', '( %s -> ( C e. NN0 /\\ ( %s ` C ) =/= %s ) )' % (A, ACC('A'), NONE))], 'simprd',
             '( %s -> ( %s ` C ) =/= %s )' % (A, ACC('A'), NONE))
    C1 = '( %s /\\ ( T ` F ) = %s )' % (A, NONE)
    e1 = w.s([w.s([w.s([w.s([], 'simpr', '( %s -> ( T ` F ) = %s )' % (C1, NONE))], 'iftrued',
                       '( %s -> %s = A )' % (C1, ACC('A')))], 'fveq1d',
                  '( %s -> ( %s ` C ) = ( A ` C ) )' % (C1, ACC('A')))], 'eqcomd',
             '( %s -> ( A ` C ) = ( %s ` C ) )' % (C1, ACC('A')))
    c1 = w.s([e1], 'orcd', '( %s -> %s )' % (C1, CONC))
    B = '( %s /\\ -. ( T ` F ) = %s )' % (A, NONE)
    nn = w.s([w.s([], 'simpr', '( %s -> -. ( T ` F ) = %s )' % (B, NONE)), w.inst('neqned')], 'syl',
             '( %s -> ( T ` F ) =/= %s )' % (B, NONE))
    ppB = w.s([pp], 'adantr', '( %s -> P e. NN0 )' % B)
    ttB = w.s([tt], 'adantr', '( %s -> T e. Tbl )' % B)
    ffB = w.s([ff], 'adantr', '( %s -> F e. NN0 )' % B)
    aaB = w.s([aa], 'adantr', '( %s -> A e. Tbl )' % B)
    llB = w.s([ll], 'adantr', '( %s -> L e. NN )' % B)
    ccB = w.s([cc], 'adantr', '( %s -> C e. NN0 )' % B)
    mz = sncl(w, B, llB, ppB, ttB, ffB, aaB)
    wc = wclstep(w, B, ppB, ttB, ffB, nn)
    ife = w.s([w.s([], 'simpr', '( %s -> -. ( T ` F ) = %s )' % (B, NONE))], 'iffalsed',
              '( %s -> %s = %s )' % (B, ACC('A'), SNA))
    ifv = w.s([ife], 'fveq1d', '( %s -> ( %s ` C ) = ( %s ` C ) )' % (B, ACC('A'), SNA))
    acB = w.s([ifv, w.s([ac], 'adantr', '( %s -> ( %s ` C ) =/= %s )' % (B, ACC('A'), NONE))], 'eqnetrrd', None)
    w.lines[-1] = w.lines[-1].split('|-')[0] + '|- ( %s -> ( %s ` C ) =/= %s )' % (B, SNA, NONE)
    cas = w.s([w.s([w.s([aaB, mz, wc], '3jca', '( %s -> ( A e. Tbl /\\ %s e. NN0 /\\ %s e. Word NN0 ) )' % (B, MOD, CSW)),
                    w.s([ccB, acB], 'jca', '( %s -> ( C e. NN0 /\\ ( %s ` C ) =/= %s ) )' % (B, SNA, NONE))], 'jca',
                   '( %s -> ( ( A e. Tbl /\\ %s e. NN0 /\\ %s e. Word NN0 ) /\\ ( C e. NN0 /\\ ( %s ` C ) =/= %s ) ) )' % (B, MOD, CSW, SNA, NONE)),
               w.inst('sincases')], 'syl',
              '( %s -> ( ( A ` C ) = ( %s ` C ) \\/ ( C = %s /\\ ( 2nd ` ( %s ` C ) ) = %s ) ) )' % (B, SNA, MOD, SNA, CSW))
    # transport the two disjuncts back across the if
    d1 = w.s([w.s([], 'simpr', '( ( %s /\\ ( A ` C ) = ( %s ` C ) ) -> ( A ` C ) = ( %s ` C ) )' % (B, SNA, SNA)),
              w.s([ifv], 'adantr', '( ( %s /\\ ( A ` C ) = ( %s ` C ) ) -> ( %s ` C ) = ( %s ` C ) )' % (B, SNA, ACC('A'), SNA))],
             'eqtr4d', '( ( %s /\\ ( A ` C ) = ( %s ` C ) ) -> ( A ` C ) = ( %s ` C ) )' % (B, SNA, ACC('A')))
    d1o = w.s([d1], 'orcd', '( ( %s /\\ ( A ` C ) = ( %s ` C ) ) -> %s )' % (B, SNA, CONC))
    D2 = '( %s /\\ ( C = %s /\\ ( 2nd ` ( %s ` C ) ) = %s ) )' % (B, MOD, SNA, CSW)
    d2a = w.s([w.s([nn], 'adantr', '( %s -> ( T ` F ) =/= %s )' % (D2, NONE)),
               w.s([w.s([], 'simpr', '( %s -> ( C = %s /\\ ( 2nd ` ( %s ` C ) ) = %s ) )' % (D2, MOD, SNA, CSW))], 'simpld',
                   '( %s -> C = %s )' % (D2, MOD))], 'jca',
              '( %s -> ( ( T ` F ) =/= %s /\\ C = %s ) )' % (D2, NONE, MOD))
    d2b = w.s([w.s([w.s([ifv], 'adantr', '( %s -> ( %s ` C ) = ( %s ` C ) )' % (D2, ACC('A'), SNA))], 'fveq2d',
                   '( %s -> ( 2nd ` ( %s ` C ) ) = ( 2nd ` ( %s ` C ) ) )' % (D2, ACC('A'), SNA)),
               w.s([w.s([], 'simpr', '( %s -> ( C = %s /\\ ( 2nd ` ( %s ` C ) ) = %s ) )' % (D2, MOD, SNA, CSW))], 'simprd',
                   '( %s -> ( 2nd ` ( %s ` C ) ) = %s )' % (D2, SNA, CSW))], 'eqtrd',
              '( %s -> ( 2nd ` ( %s ` C ) ) = %s )' % (D2, ACC('A'), CSW))
    d2o = w.s([w.s([d2a, d2b], 'jca', '( %s -> ( ( ( T ` F ) =/= %s /\\ C = %s ) /\\ ( 2nd ` ( %s ` C ) ) = %s ) )' % (D2, NONE, MOD, ACC('A'), CSW))],
              'olcd', '( %s -> %s )' % (D2, CONC))
    c2 = w.s([cas, w.s([d1o], 'ex', '( %s -> ( ( A ` C ) = ( %s ` C ) -> %s ) )' % (B, SNA, CONC)),
              w.s([d2o], 'ex', '( %s -> ( ( C = %s /\\ ( 2nd ` ( %s ` C ) ) = %s ) -> %s ) )' % (B, MOD, SNA, CSW, CONC))],
             'mpjaod', '( %s -> %s )' % (B, CONC))
    w.qed([c1, c2], 'pm2.61dan', '( %s -> %s )' % (A, CONC))
    run(w)
