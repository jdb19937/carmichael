"""T7b: append the installation predicates (syntax + df-) of the named
fragments to the sortie file.  Usage: MM_DB=sorties/t7b.mm python3
tools/gen/t7b_a_defs.py NAME...  (skips a predicate already defined)."""
import sys, os, textwrap
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t7blib import *

DBP = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))),
                   os.environ.get('MM_DB', 'carmichael.mm'))


def wrap(text, indent):
    return textwrap.fill(text, 79, initial_indent=indent, subsequent_indent=indent + '  ',
                         break_long_words=False, break_on_hyphens=False)


def block(f, extra_comment=''):
    c = f.const
    lab = c.lower()
    stk = ' '.join(f.stacks)
    syn = ('  $c %s $.\n' % c +
           wrap('$( Extend wff notation: the fragment ` %s ` installed.  %s $)' % (f.name, extra_comment), '  ') + '\n' +
           '  w%s $a wff %s $.\n' % (lab, f.pred()))
    com = ('$( Definition of the installation predicate of Lean\'s fragment %s with stack parameters '
           '` %s ` : it is installed in the machine ` ( T , M ) ` at the label function ` P ` with exit '
           '` E ` (Lean ` Frag.Installed F M iota e ` , ` iota = P ` ) when the program equations of its '
           'own labels ` ( P `` 0 ) ` , ` ( P `` 1 ) ` , ... hold (entry ` ( P `` 0 ) ` ) and its labels, '
           'the exit included, are labels of the machine. $)' % (f.lean, stk))
    df = 'df-%s $a |- %s $.' % (lab, f.df())
    toks = f.df().split()
    dums = sorted(set(t for t in toks if len(t) == 1 and t.islower()))
    vs = sorted(set(t for t in toks if t in f.stacks or t in ('T', 'M', 'P', 'E')))
    if not dums:
        return syn + '\n' + wrap(com, '  ') + '\n' + wrap(df, '  ') + '\n'
    dline = '    ' + '  '.join('$d %s %s $.' % (' '.join(dums), v) for v in vs)
    return (syn + '  ${\n' + dline + '\n' + wrap(com, '    ') + '\n' + wrap(df, '    ') + '\n  $}\n')


def main(names):
    txt = open(DBP).read()
    out = []
    for n in names:
        f = FRAGS[n]
        if ('df-%s $a' % f.const.lower()) in txt:
            print('skip', n); continue
        out.append(block(f))
    if out:
        with open(DBP, 'a') as fh:
            fh.write('\n' + '\n'.join(out))
        print('appended', len(out))


if __name__ == '__main__':
    main(sys.argv[1:])
