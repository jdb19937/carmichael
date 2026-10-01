"""Sortie A3b helpers: the shared antecedent texts of the windowed pointwise
lemmas and the extraction of their basic facts."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
import a3lib          # a1lib parser extensions (prod_, InWindow, decimals)
from tm import W
import num

# ---------------------------------------------------------------- the texts
def A(N='N'): return '( ell2 ` %s )' % N
def B(N='N'): return '( ell3 ` %s )' % N

HC1 = '( C e. RR /\\ ; ; ; 1 0 0 0 <_ C )'
HC2 = '( E e. RR /\\ 0 < E /\\ E <_ ( 1 / 2 ) )'
HC = '( %s /\\ %s )' % (HC1, HC2)

def NS(N='N'):
    a, b = A(N), B(N)
    return ['%s e. ( ZZ>= ` 3 )' % N,
            '; 5 0 <_ %s' % a,
            '1 <_ %s' % b,
            '( log ` ( 4 x. C ) ) <_ %s' % b,
            '( %s ^ 2 ) <_ ( %s ^c ( E / 4 ) )' % (b, a),
            '( ; ; ; 9 6 0 0 x. C ) <_ ( %s ^c ( ( 3 x. E ) / 4 ) )' % a,
            '; ; ; 1 2 0 0 <_ ( %s ^c ( 1 - ( E / 4 ) ) )' % a,
            '( ; 1 6 x. ( %s ^ 2 ) ) <_ ( exp ` ( ( 3 / ; ; 1 0 0 ) x. %s ) )' % (a, a)]

def HN(N='N'):
    n = NS(N)
    return '( ( %s /\\ %s /\\ %s ) /\\ ( %s /\\ %s ) /\\ ( %s /\\ %s /\\ %s ) )' % (
        n[0], n[1], n[2], n[3], n[4], n[5], n[6], n[7])

def N5(N='N'):
    return NS(N)[4]

def IW(N='N', Z='Z', W='W', Y='Y', T='T'):
    return '<. <. C , E >. , %s >. InWindow <. <. %s , %s >. , <. %s , %s >. >.' % (N, Z, W, Y, T)

P2 = '( ( ( Z ^ ( Y + 1 ) ) x. ( 1 + ( T x. ( log ` Z ) ) ) ) + 2 )'
G = '( ( ( 3 / 2 ) x. ( ell2 ` N ) ) x. ( ell3 ` N ) )'
GW = '( ( Z goodPrimesW W ) ` Y )'
PL = '( ( Q pool Z ) ` K )'
L = '( Lmod ` Q )'


# ------------------------------------------------------- fact extraction
def basefacts(w, ANT, hc, hn, iw, N='N'):
    """dict of steps for every basic consequence of ( ANT -> HC /\\ HN /\\ IW )"""
    a, b = A(N), B(N)
    n = NS(N)
    d = {'hc': hc, 'hn': hn, 'iw': iw}
    def st(hyps, ref, f):
        return w.s(hyps, ref, '( %s -> %s )' % (ANT, f))
    d['hc1'] = st([hc], 'simpld', HC1)
    d['hc2'] = st([hc], 'simprd', HC2)
    d['cre'] = st([d['hc1']], 'simpld', 'C e. RR')
    d['c1k'] = st([d['hc1']], 'simprd', '; ; ; 1 0 0 0 <_ C')
    d['ere'] = st([d['hc2']], 'simp1d', 'E e. RR')
    d['e0'] = st([d['hc2']], 'simp2d', '0 < E')
    d['eh'] = st([d['hc2']], 'simp3d', 'E <_ ( 1 / 2 )')
    hn1 = st([hn], 'simp1d', '( %s /\\ %s /\\ %s )' % (n[0], n[1], n[2]))
    hn2 = st([hn], 'simp2d', '( %s /\\ %s )' % (n[3], N5(N)))
    hn3 = st([hn], 'simp3d', '( %s /\\ %s /\\ %s )' % (n[5], n[6], n[7]))
    d['n1'] = st([hn1], 'simp1d', n[0])
    d['n2'] = st([hn1], 'simp2d', n[1])
    d['n3'] = st([hn1], 'simp3d', n[2])
    d['n4'] = st([hn2], 'simpld', n[3])
    d['n5'] = st([hn2], 'simprd', N5(N))
    d['n6'] = st([hn3], 'simp1d', n[5])
    d['n7'] = st([hn3], 'simp2d', n[6])
    d['n8'] = st([hn3], 'simp3d', n[7])
    # typing from the window relation
    typ = st([iw, w.inst('inwintyp')], 'syl',
             '( ( C e. RR /\\ E e. RR /\\ %s e. NN0 ) /\\ ( Z e. NN0 /\\ W e. NN0 ) /\\ ( Y e. NN0 /\\ T e. NN0 ) )' % N)
    d['nn0'] = st([typ, w.inst('simp13')], 'syl', '%s e. NN0' % N)
    d['zn0'] = st([typ, w.inst('simp2l')], 'syl', 'Z e. NN0')
    d['wn0'] = st([typ, w.inst('simp2r')], 'syl', 'W e. NN0')
    d['yn0'] = st([typ, w.inst('simp3l')], 'syl', 'Y e. NN0')
    d['tn0'] = st([typ, w.inst('simp3r')], 'syl', 'T e. NN0')
    d['zre'] = st([d['zn0']], 'nn0red', 'Z e. RR')
    d['tre'] = st([d['tn0']], 'nn0red', 'T e. RR')
    # A, B real, B = log A
    d['uz2'] = st([d['n1'], w.inst('uzuzle23')], 'syl', '%s e. ( ZZ>= ` 2 )' % N)
    d['are'] = st([d['uz2'], w.inst('ell2cl')], 'syl', '%s e. RR' % a)
    d['bre'] = st([d['n1'], w.inst('ell3cl')], 'syl', '%s e. RR' % b)
    d['beq'] = st([d['nn0'], w.inst('ell3val')], 'syl', '%s = ( log ` %s )' % (b, a))
    d['arb'] = st([d['are'], d['n2']], 'jca', '( %s e. RR /\\ ; 5 0 <_ %s )' % (a, a))
    d['br1'] = st([d['bre'], d['n3']], 'jca', '( %s e. RR /\\ 1 <_ %s )' % (b, b))
    # window projections
    d['zlo'] = st([iw, w.inst('inwinzlo')], 'syl', '( ( C x. %s ) x. %s ) <_ Z' % (a, b))
    d['zhi'] = st([iw, w.inst('inwinzhi')], 'syl', 'Z <_ ( 4 x. ( ( C x. %s ) x. %s ) )' % (a, b))
    d['wlo'] = st([iw, w.inst('inwinwlo')], 'syl', '( Z ^c ( ; 9 9 / ; ; 1 0 0 ) ) <_ ( W + 1 )')
    d['yhi'] = st([iw, w.inst('inwinyhi')], 'syl', 'Y <_ ( 4 x. ( Z ^c ( 1 - E ) ) )')
    d['tlo'] = st([iw, w.inst('inwintlo')], 'syl', '( 3 x. %s ) <_ T' % a)
    d['thi'] = st([iw, w.inst('inwinthi')], 'syl', 'T <_ ( 5 x. %s )' % a)
    return d


def relay(w, ANTX, anl, N='N'):
    """basefacts for a wider antecedent ANTX, given anl : ( ANTX -> HC /\\ HN /\\ IW )"""
    hc = w.s([anl], 'simp1d', '( %s -> %s )' % (ANTX, HC))
    hn = w.s([anl], 'simp2d', '( %s -> %s )' % (ANTX, HN(N)))
    iw = w.s([anl], 'simp3d', '( %s -> %s )' % (ANTX, IW(N)))
    return basefacts(w, ANTX, hc, hn, iw, N)


def zfacts(w, ANT, d, zb):
    """Z e. NN, Z e. RR+, ( log ` Z ) e. RR, 0 <_ ( log ` Z ), 1 <_ Z from
    zb : ( ANT -> ( 1 < Z /\\ B <_ ( log ` Z ) /\\ ( log ` Z ) <_ ( 3 x. B ) ) )"""
    def st(hyps, ref, f):
        return w.s(hyps, ref, '( %s -> %s )' % (ANT, f))
    z1lt = st([zb], 'simp1d', '1 < Z')
    z1 = st([z1lt], 'ltled', '1 <_ Z')
    znn = st([d['zn0'], z1, w.inst('elnnnn0c')], 'sylanbrc', 'Z e. NN')
    zrp = st([znn], 'nnrpd', 'Z e. RR+')
    lzre = st([zrp], 'relogcld', '( log ` Z ) e. RR')
    lz0 = st([d['zre'], z1, w.inst('logge0')], 'syl2anc', '0 <_ ( log ` Z )')
    return dict(z1lt=z1lt, z1=z1, znn=znn, zrp=zrp, lzre=lzre, lz0=lz0,
                blz=st([zb], 'simp2d', '%s <_ ( log ` Z )' % B()),
                lzub=st([zb], 'simp3d', '( log ` Z ) <_ ( 3 x. %s )' % B()))


def dbstmt(label):
    """the statement of a theorem already in the database, whitespace-normalised"""
    import subprocess, os
    env = dict(os.environ)
    out = subprocess.run(['python3', 'tools/mm.py', 'show', label], capture_output=True,
                         text=True, env=env, cwd=os.path.dirname(os.path.dirname(
                             os.path.dirname(os.path.abspath(__file__))))).stdout
    body = out.split(' $p ', 1)[1].split('$=')[0]
    body = ' '.join(body.split())
    assert body.startswith('|- '), body[:40]
    return body[3:].strip()


def dbconcl(label):
    """the consequent of a theorem of the form ( ANT -> CONCL )"""
    s = dbstmt(label)
    assert s.startswith('( ') and s.endswith(' )'), s[:40]
    t = s[2:-2].strip()
    toks = t.split(' ')
    depth = 0
    for i, x in enumerate(toks):
        if x in ('(', '{', '<.'):
            depth += 1
        elif x in (')', '}', '>.'):
            depth -= 1
        elif x == '->' and depth == 0:
            return ' '.join(toks[i + 1:])
    raise ValueError('no top-level -> in ' + label)


def subvars(text, m):
    """token-level variable substitution in a formula"""
    return ' '.join(m.get(t, t) for t in text.split(' '))


def evan3(w, ante, steps, texts, EV):
    """three eventual facts combined into the 3-fold conjunction ( t1 /\\ t2 /\\ t3 )"""
    t1, t2, t3 = texts
    s12 = w.s([steps[0], steps[1]], 'evan2', '( %s -> %s )' % (ante, EV('( %s /\\ %s )' % (t1, t2))))
    s123 = w.s([s12, steps[2]], 'evan2', '( %s -> %s )' % (ante, EV('( ( %s /\\ %s ) /\\ %s )' % (t1, t2, t3))))
    P = '( %s /\\ ( ( %s /\\ %s ) /\\ %s ) )' % (ante, t1, t2, t3)
    p1 = w.s([], 'simprll', '( %s -> %s )' % (P, t1))
    p2 = w.s([], 'simprlr', '( %s -> %s )' % (P, t2))
    p3 = w.s([], 'simprr', '( %s -> %s )' % (P, t3))
    tri = w.s([p1, p2, p3], '3jca', '( %s -> ( %s /\\ %s /\\ %s ) )' % (P, t1, t2, t3))
    return w.s([s123, tri], 'evimd', '( %s -> %s )' % (ante, EV('( %s /\\ %s /\\ %s )' % (t1, t2, t3))))
