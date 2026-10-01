"""T11 (scan): the per-iteration charge identity of the scan loop, over letters (so that the conversions
~ tmiscia / ~ tmiscib / ~ tmiscic cite it instead of running ` lineq ` under their 3 KB antecedent).

  tmscuba   ` a = b + c + 1 ` : ` ( c + 1 ) u - 1 = ( u a - u b ) - 1 ` , and the latter is in NN0 (` u e. NN `)
  tmscubb   ` a = b + c + d + 1 ` : ` ( c + d + 1 ) u - 1 = ( u a - u b ) - 1 ` , in NN0
  tmscubc   ` a = c + d + 1 ` , ` b = 0 ` : the same

    MM_DB=sorties/t11.mm python3 tools/gen/t11s_f_ub.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t11lib import *
from lin import linarith, lineq
from cl import Closure
import t6blib

SEL = sys.argv[1:]
UO = os.environ.get('T11S_UO') == '1'
STMTS = {}
TREES = {}


def add(label, tree, concl_):
    STMTS[label] = '( %s -> %s )' % (cj(tree), concl_)
    TREES[label] = (tree, concl_)
    t6blib._STMT[label] = STMTS[label]


RHS = '( ( ( U x. A ) - ( U x. B ) ) - 1 )'
LHS = {'a': '( ( ( C + 1 ) x. U ) - 1 )', 'b': '( ( ( ( C + D ) + 1 ) x. U ) - 1 )'}
LHS['c'] = LHS['b']
H3 = ('U e. NN', 'A e. NN0', 'B e. NN0')
TREE = {'a': (H3, ('C e. NN0', 'A = ( ( B + C ) + 1 )')),
        'b': (H3, (('C e. NN0', 'D e. NN0'), 'A = ( ( ( B + C ) + D ) + 1 )')),
        'c': (H3, (('C e. NN0', 'D e. NN0'), ('A = ( ( C + D ) + 1 )', 'B = 0')))}
for _k in 'abc':
    add('tmscub' + _k, TREE[_k], '( %s = %s /\\ %s e. NN0 )' % (LHS[_k], RHS, RHS))

# the arithmetic of an iteration ` i < R ` (fuel ` H - i ` , ` k + i ` ) below ` 2 ^ B `
T_ARI = (('G e. NN0', 'H e. NN0', 'R e. NN0'), (('i e. NN0', '( i + 1 ) <_ R'), ('R <_ H', 'B e. NN0')), '( G + H ) < ( 2 ^ B )')
C_ARI = ('( ( ( H - i ) = ( ( H - ( i + 1 ) ) + 1 ) /\\ ( ( G + ( i + 1 ) ) - 1 ) = ( G + i ) ) /\\ '
         '( ( ( G + i ) + 1 ) < ( 2 ^ B ) /\\ ( ( H - ( i + 1 ) ) + 1 ) < ( 2 ^ B ) ) )')
add('tmscari', T_ARI, C_ARI)


def ub_proof(lab):
    kind = lab[-1]
    T = TREE[kind]
    ph = cj(T)
    w = W(lab, 'The charge of one iteration of the scan loop at the machine (~ tmiscia , ~ tmiscib , ~ tmiscic ): the body\'s '
               'bound ` ( %s + 1 ) u - 1 ` is ` u a - u b - 1 ` with ` a ` , ` b ` the scan costs before and after the iteration '
               '(~ tmscv%s ), a number.' % ('c' if kind == 'a' else 'c + d', kind))
    s = w.s
    c = Ctx(w, ph, T)
    un, an, bn = c['U e. NN'], c['A e. NN0'], c['B e. NN0']
    cl = Closure(w, ph, {'U': ('NN', un), 'A': ('NN0', an), 'B': ('NN0', bn), 'C': ('NN0', c['C e. NN0'])})
    # the equations multiplied by U (linarith does not multiply a hypothesis by an atom)
    mulu = lambda e, x, y: s([e], 'oveq2d', '( %s -> ( U x. %s ) = ( U x. %s ) )' % (ph, x, y))
    hyps = []
    if kind == 'a':
        hyps.append(mulu(c['A = ( ( B + C ) + 1 )'], 'A', '( ( B + C ) + 1 )'))
    else:
        cl.leaf('D', 'NN0', c['D e. NN0'])
        if kind == 'b':
            hyps.append(mulu(c['A = ( ( ( B + C ) + D ) + 1 )'], 'A', '( ( ( B + C ) + D ) + 1 )'))
        else:
            hyps.append(mulu(c['A = ( ( C + D ) + 1 )'], 'A', '( ( C + D ) + 1 )'))
            ub0 = s([mulu(c['B = 0'], 'B', '0'), s([cl.mem('U', 'CC')], 'mul01d', '( %s -> ( U x. 0 ) = 0 )' % ph)], 'eqtrd',
                     '( %s -> ( U x. B ) = 0 )' % ph)
            hyps.append(ub0)
    u1 = s([un, w.inst('nnge1')], 'syl', '( %s -> 1 <_ U )' % ph)
    cu = s([cl.mem('C', 'RR'), cl.mem('U', 'RR'), cl.ge0('C'), cl.ge0('U')], 'mulge0d', '( %s -> 0 <_ ( C x. U ) )' % ph)
    hy2 = [u1, cu]
    if kind != 'a':
        hy2.append(s([cl.mem('D', 'RR'), cl.mem('U', 'RR'), cl.ge0('D'), cl.ge0('U')], 'mulge0d', '( %s -> 0 <_ ( D x. U ) )' % ph))
    L, Rr = LHS[kind], RHS
    eq = lineq(w, ph, L, Rr, hyps=hyps, closure=cl, products=True)
    ge = linarith(w, ph, hy2, '0 <_ %s' % L, closure=cl, products=True)
    ln = s([s([cl.mem(L, 'ZZ'), ge], 'jca', '( %s -> ( %s e. ZZ /\\ 0 <_ %s ) )' % (ph, L, L)),
            s([], 'elnn0z', '( %s e. NN0 <-> ( %s e. ZZ /\\ 0 <_ %s ) )' % (L, L, L))], 'sylibr', '( %s -> %s e. NN0 )' % (ph, L))
    rn = s([eq, ln], 'eqeltrrd', '( %s -> %s e. NN0 )' % (ph, Rr))
    w.qed([eq, rn], 'jca', STMTS[lab])
    return w.run(unify_only=UO)


def tmscari():
    lab = 'tmscari'
    T = T_ARI
    ph = cj(T)
    w = W(lab, 'The arithmetic of an iteration ` i < R ` of the scan loop at the machine (~ tmiscia , ~ tmiscib , ~ tmiscic ): the '
               'fuel ` H - i ` is ` ( H - ( i + 1 ) ) + 1 ` , ` ( G + ( i + 1 ) ) - 1 = G + i ` , and ` G + i + 1 ` , '
               '` H - ( i + 1 ) + 1 ` are below ` 2 ^ B ` .')
    s = w.s
    c = Ctx(w, ph, T)
    cl = Closure(w, ph, {'G': ('NN0', c['G e. NN0']), 'H': ('NN0', c['H e. NN0']), 'R': ('NN0', c['R e. NN0']),
                         'i': ('NN0', c['i e. NN0'])})
    P2B = '( 2 ^ B )'
    cl.leaf(P2B, 'RR', s([s([closed(w, ph, '2nn', '2 e. NN'), c['B e. NN0'], w.inst('nnexpcl')], 'syl2anc', '( %s -> %s e. NN )' % (ph, P2B))],
                         'nnred', '( %s -> %s e. RR )' % (ph, P2B)))
    e1 = lineq(w, ph, '( H - i )', '( ( H - ( i + 1 ) ) + 1 )', closure=cl)
    e2 = lineq(w, ph, '( ( G + ( i + 1 ) ) - 1 )', '( G + i )', closure=cl)
    ghb, i1le, rle = c['( G + H ) < ( 2 ^ B )'], c['( i + 1 ) <_ R'], c['R <_ H']
    l1 = linarith(w, ph, [ghb, i1le, rle], '( ( G + i ) + 1 ) < %s' % P2B, closure=cl)
    l2 = linarith(w, ph, [ghb, cl.ge0('G'), cl.ge0('i')], '( ( H - ( i + 1 ) ) + 1 ) < %s' % P2B, closure=cl)
    w.qed([s([e1, e2], 'jca', '( %s -> %s )' % (ph, cj(parse_conj(C_ARI)[0]))), s([l1, l2], 'jca', '( %s -> %s )' % (ph, cj(parse_conj(C_ARI)[1])))],
          'jca', STMTS[lab])
    return w.run(unify_only=UO)


def tmscuba(): return ub_proof('tmscuba')
def tmscubb(): return ub_proof('tmscubb')
def tmscubc(): return ub_proof('tmscubc')


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
