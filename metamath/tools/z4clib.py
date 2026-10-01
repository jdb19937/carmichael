"""Sortie Z4c helpers (Route Z: LargeSieve.lean 1124-1350, the totient-quotient
weight, and window_sieve's step 1 + assembly).

STATEMENTS is the frozen text of Z4c-blueprint.md section 3.
`MM_DB=sorties/z4c.mm MM_ENGINE=mmatch python3 tools/z4clib.py [LABEL...]`
grammar-checks them (a hypothesis + `idi` worksheet unified by mmatch, as C10 did).
"""
import sys, os, re, subprocess
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import z4blib as Z
from z4blib import Q0, Q0S, RF, HWIN, BLK, SW, WR


def CS(K, Wb, x='x'):
    """Lean coprimeSetM K Wb (V3's CS)"""
    return '{ %s e. ( 1 ... %s ) | ( %s gcd %s ) = 1 }' % (x, Wb, x, K)


def RAD(J):
    """Lean radd J (V4b's RAD: product binder e, set-builder binder u)"""
    return 'prod_ e e. { u e. Prime | u || %s } e' % J


def TS(Wb, F, r='r'):
    """Lean (Icc 1 Wb).filter (Squarefree r /\\ Coprime r F)"""
    return '{ %s e. ( 1 ... %s ) | ( ( mmu ` %s ) =/= 0 /\\ ( %s gcd %s ) = 1 ) }' % (r, Wb, r, r, F)


FLA = '( |_ ` A )'
HARM = 'sum_ m e. ( 1 ... W ) ( 1 / m )'
PRQ = 'prod_ q e. { r e. Prime | r || L } ( 1 / ( 1 - ( 1 / q ) ) )'

STATEMENTS = {}
STATEMENTS['cophrmh'] = '( ( K e. NN /\\ W e. NN ) -> %s <_ ( ( K / ( phi ` K ) ) x. sum_ j e. %s ( 1 / j ) ) )' % (HARM, CS('K', 'W'))
STATEMENTS['cophrmfl'] = '( ( K e. NN /\\ A e. RR /\\ 1 <_ A ) -> ( ( ( phi ` K ) / K ) x. ( log ` A ) ) <_ sum_ j e. %s ( 1 / j ) )' % CS('K', FLA)
STATEMENTS['phiinvpf'] = '( L e. NN -> ( ( 1 / L ) x. %s ) = ( 1 / ( phi ` L ) ) )' % PRQ
STATEMENTS['radfib'] = '( ( X e. NN /\\ ( D e. NN /\\ ( mmu ` D ) =/= 0 ) ) -> sum_ j e. %s if ( D = %s , ( 1 / j ) , 0 ) <_ ( 1 / ( phi ` D ) ) )' % (CS('F', 'X'), RAD('j'))
STATEMENTS['sumphiinv'] = '( ( F e. NN /\\ A e. RR /\\ 1 <_ A ) -> ( ( ( phi ` F ) / F ) x. ( log ` A ) ) <_ sum_ r e. %s ( 1 / ( phi ` r ) ) )' % TS(FLA, 'F')
STATEMENTS['lswinset'] = '( ( Q e. RR /\\ f e. %s ) -> %s C_ %s )' % (Q0S, TS('( |_ ` ( Q / f ) )', 'f'), RF(Q0))
STATEMENTS['lswinw'] = Z.LATER['lswinw']
STATEMENTS['lswsieve'] = Z.LATER['lswsieve']


def gramcheck(labels):
    out = {}
    for lab in labels:
        f = STATEMENTS[lab]
        path = 'worksheets/z4cgc%s.mmp' % lab
        with open(path, 'w') as fh:
            fh.write('$( <MM> <PROOF_ASST> THEOREM=z4cgc%s  LOC_AFTER=?\n\n* gc\n\n'
                     'h1::z4cgc%s.1 |- %s\nqed:1:idi |- %s\n$)\n' % (lab, lab, f, f))
        env = dict(os.environ, MM_ENGINE='mmatch')
        r = subprocess.run(['python3', 'tools/mm.py', 'unify', path], capture_output=True, text=True, env=env)
        out[lab] = 'UNIFY OK' in r.stdout
        if out[lab]:
            os.remove(path)
        else:
            print(r.stdout[-1500:], r.stderr[-800:])
    return out


if __name__ == '__main__':
    for lab, ok in gramcheck(sys.argv[1:] or list(STATEMENTS)).items():
        print(('OK   ' if ok else 'BAD  ') + lab)
