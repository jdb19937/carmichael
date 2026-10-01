"""Sortie v2: the frozen statements of the Selberg sieve block (SelbergBound.lean).

Each statement is written to scratch/v2sel/LABEL.mmp as a worksheet whose qed line is
the statement and which has no proof; `MM_DB=sorties/v2.mm python3 tools/mm.py unify` on
it is the grammar check (mmj2 parses every step; only I-PA-0411 "step incomplete" is
expected).  The statements are the frozen interface for sortie V3.
"""
import os, subprocess, sys
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
OUT = os.path.join(ROOT, 'scratch', 'v2sel')

DVP = '{ x e. NN | x || P }'
def DV(v): return '{ x e. NN | x || %s }' % v
def PFD(v): return '{ r e. Prime | r || %s }' % v

# the sieve data
SH = ('( ( ( A e. Fin /\\ A C_ NN /\\ W : NN --> RR ) /\\ '
      '( A. k e. NN 0 <_ ( W ` k ) /\\ X e. RR /\\ ( Y e. RR /\\ 1 <_ Y ) ) ) /\\ '
      '( ( P e. NN /\\ ( mmu ` P ) =/= 0 ) /\\ '
      '( V : NN --> RR /\\ ( V ` 1 ) = 1 /\\ '
      '( A. a e. NN A. b e. NN ( ( a gcd b ) = 1 -> '
      '( V ` ( a x. b ) ) = ( ( V ` a ) x. ( V ` b ) ) ) /\\ '
      'A. s e. Prime ( s || P -> ( 0 < ( V ` s ) /\\ ( V ` s ) < 1 ) ) ) ) ) )')

# the derived quantities
def GT(v, b='q'):
    return '( ( V ` %s ) x. prod_ %s e. { r e. Prime | r || %s } ( 1 / ( 1 - ( V ` %s ) ) ) )' % (v, b, v, b)
SS = 'sum_ l e. %s if ( ( l ^ 2 ) <_ Y , %s , 0 )' % (DVP, GT('l'))
def MS(v): return 'sum_ n e. A if ( %s || n , ( W ` n ) , 0 )' % v
def RM(v): return '( %s - ( ( V ` %s ) x. X ) )' % (MS(v), v)
SF = 'sum_ n e. A if ( ( P gcd n ) = 1 , ( W ` n ) , 0 )'
def LW(v):
    return ('if ( %s || P , ( ( ( ( 1 / ( V ` %s ) ) x. %s ) x. ( ( mmu ` %s ) x. ( 1 / %s ) ) ) x. '
            'sum_ m e. %s if ( ( ( ( %s x. m ) ^ 2 ) <_ Y /\\ ( m gcd %s ) = 1 ) , %s , 0 ) ) , 0 )'
            % (v, v, GT(v), v, SS, DVP, v, v, GT('m')))
def MP(v):
    return ('sum_ d e. %s sum_ e e. %s if ( %s = ( d lcm e ) , ( %s x. %s ) , 0 )'
            % (DV(v), DV(v), v, LW('d'), LW('e')))
ERR = ('sum_ d e. %s if ( d <_ Y , ( ( 3 ^ ( # ` %s ) ) x. ( abs ` %s ) ) , 0 )'
       % (DVP, PFD('d'), RM('d')))
# a generic upper-Moebius sequence U and a generic weight sequence L
# the upper-Moebius hypothesis quantifies over y with inner variable e, so that the
# summation variables n and d of the conclusion do not occur in the antecedent
UPM = ('( U : NN --> RR /\\ A. y e. NN if ( y = 1 , 1 , 0 ) <_ sum_ e e. { x e. NN | x || y } ( U ` e ) )')
def LS(v):
    return ('sum_ d e. %s sum_ e e. %s if ( %s = ( d lcm e ) , ( ( L ` d ) x. ( L ` e ) ) , 0 )'
            % (DV(v), DV(v), v))

STMTS = {
  # the truncated Moebius inversion
  'muinvdvds': ('The truncated Moebius sum over the divisors of a squarefree number that are '
                'multiples of L detects L = M.',
     '( ( M e. NN /\\ ( mmu ` M ) =/= 0 /\\ L e. NN ) -> '
     'sum_ d e. %s if ( L || d , ( mmu ` d ) , 0 ) = if ( L = M , ( mmu ` L ) , 0 ) )' % DV('M')),
  # the Lambda-squared sieve is upper Moebius
  'lamsqub': ('The Lambda squared coefficients of a weight sequence with L ( 1 ) = 1 are upper '
              'Moebius.',
     '( ( L : NN --> RR /\\ ( L ` 1 ) = 1 /\\ N e. NN ) -> '
     'if ( N = 1 , 1 , 0 ) <_ sum_ d e. %s %s )' % (DV('N'), LS('d'))),
  # the fundamental sieve inequality for any upper-Moebius sequence
  'siftub': ('The sifted sum is at most the main term plus the error term of any upper Moebius '
             'sequence.',
     '( ( %s /\\ %s ) -> %s <_ ( ( X x. sum_ d e. %s ( ( U ` d ) x. ( V ` d ) ) ) + '
     'sum_ d e. %s ( ( abs ` ( U ` d ) ) x. ( abs ` %s ) ) ) )'
     % (SH, UPM, SF, DVP, DVP, RM('d'))),
  # the Selberg terms and the bounding sum
  'gtpos': ('The Selberg term of a divisor of the sifting product is positive.',
     '( ( %s /\\ L || P ) -> 0 < %s )' % (SH, GT('L'))),
  'sspos': ('The Selberg bounding sum is positive.', '( %s -> 0 < %s )' % (SH, SS)),
  # the Selberg weights
  'lwdvds': ('The key identity of the Selberg weights.',
     '( ( %s /\\ D e. NN ) -> ( ( V ` D ) x. %s ) = '
     '( ( ( 1 / %s ) x. ( mmu ` D ) ) x. sum_ l e. %s if ( ( D || l /\\ ( l ^ 2 ) <_ Y ) , %s , 0 ) ) )'
     % (SH, LW('D'), SS, DVP, GT('l'))),
  'lwdiag': ('Diagonalisation of the Selberg weights.',
     '( ( %s /\\ L || P ) -> sum_ d e. %s if ( L || d , ( ( V ` d ) x. %s ) , 0 ) = '
     'if ( ( L ^ 2 ) <_ Y , ( ( %s x. ( mmu ` L ) ) x. ( 1 / %s ) ) , 0 ) )'
     % (SH, DVP, LW('d'), GT('L'), SS)),
  'lwabs': ('The Selberg weights are bounded by one in absolute value.',
     '( ( %s /\\ D e. NN ) -> ( abs ` %s ) <_ 1 )' % (SH, LW('D'))),
  'mpmain': ('The main term of the Selberg Lambda squared sieve is one over the bounding sum.',
     '( %s -> sum_ d e. %s ( %s x. ( V ` d ) ) = ( 1 / %s ) )' % (SH, DVP, MP('d'), SS)),
  'mp0': ('The Selberg Lambda squared coefficients vanish above the level.',
     '( ( %s /\\ D e. NN /\\ -. D <_ Y ) -> %s = 0 )' % (SH, MP('D'))),
  # the 3 ^ omega count
  'lcmcnt': ('The number of pairs of divisors of a squarefree number with least common multiple '
             'the number itself is three to the number of prime divisors.',
     '( ( N e. NN /\\ ( mmu ` N ) =/= 0 ) -> '
     'sum_ d e. %s sum_ e e. %s if ( N = ( d lcm e ) , 1 , 0 ) = ( 3 ^ ( # ` %s ) ) )'
     % (DV('N'), DV('N'), PFD('N'))),
  'mpabs': ('The Selberg Lambda squared coefficients are bounded by three to the number of prime '
            'divisors.',
     '( ( %s /\\ N || P ) -> ( abs ` %s ) <_ ( 3 ^ ( # ` %s ) ) )' % (SH, MP('N'), PFD('N'))),
  'selberr': ('The error term of the Selberg sieve.',
     '( %s -> sum_ d e. %s ( ( abs ` %s ) x. ( abs ` %s ) ) <_ %s )'
     % (SH, DVP, MP('d'), RM('d'), ERR)),
  # the fundamental theorem
  'selbsieve': ('The fundamental theorem of the Selberg sieve.',
     '( %s -> %s <_ ( ( X / %s ) + %s ) )' % (SH, SF, SS, ERR)),
}


def write(label):
    os.makedirs(OUT, exist_ok=True)
    desc, st = STMTS[label]
    path = os.path.join(OUT, label + '.mmp')
    with open(path, 'w') as f:
        f.write('$( <MM> <PROOF_ASST> THEOREM=%s  LOC_AFTER=?\n\n* %s\n\n' % (label, desc))
        f.write('qed:: |- %s\n' % st)
        f.write('$)\n')
    return path


def check(label):
    path = write(label)
    r = subprocess.run([sys.executable, os.path.join(ROOT, 'tools', 'mm.py'), 'unify', path],
                       cwd=ROOT, capture_output=True, text=True)
    out = r.stdout + r.stderr
    bad = [l for l in out.split('\n') if l.startswith('E-')]
    print(('PARSE OK   ' if not bad else 'PARSE FAIL ') + label)
    for l in bad[:4]:
        print('   ' + l[:200])
    return not bad


if __name__ == '__main__':
    labels = sys.argv[1:] or list(STMTS)
    ok = all(check(l) for l in labels)
    sys.exit(0 if ok else 1)
