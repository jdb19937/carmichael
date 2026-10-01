"""T7c: T6b's ` copyList ` chain with the ` move2Num ` handler apart from the labels.

~ tm2lcpyb , ~ tm2lcpyl , ~ tm2lcpy , ~ tm2lcpyn , ~ tm2lcpyb2 use the class
variable F0 both for a label (the ` pushSym x comma ` of the body's
` moveEntry ` , ` ( M ` F0 ) ` ) and for the pop handler of ` dup ` 's
` move2Num ` ( ` ( M ` L0 ) = pop I F0 ... ` , ` F0 e. ( ( 2nd ` T ) ^m ... ) ` ),
so an instance needs a label equal to a handler.  This driver runs the same
generators (tools/gen/t6b_e_cpy.py, tools/gen/tmd_a_cpyn.py) with every
worksheet formula rewritten: the handler occurrences of F0 become G, and the
cited copyList theorems their G forms.

    MM_DB=sorties/t7c.mm python3 tools/gen/t7c_i_cpyg.py [LABEL...]
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import tm

RENAME = {'tm2lcpyb': 'tm2lcpybg', 'tm2lcpyl': 'tm2lcpylg', 'tm2lcpy': 'tm2lcpyg',
          'tm2lcpyn': 'tm2lcpyng', 'tm2lcpyb2': 'tm2lcpyb2g'}


def handler_f0(toks):
    """rewrite the handler occurrences of F0 to G; label occurrences stay"""
    out = list(toks)
    for i, t in enumerate(toks):
        if t != 'F0':
            continue
        nx = toks[i + 1:i + 4]
        pv = toks[max(0, i - 7):i]
        if nx[:1] == ['`']:
            out[i] = 'G'
        elif nx[:3] == ['e.', '(', '(']:
            out[i] = 'G'
        elif len(pv) == 7 and pv[-1] == '<.' and pv[-2] == ',' and pv[-4] == '<.' and pv[-5] == ',' and pv[-6] == '2' and pv[-7] == '<.':
            out[i] = 'G'
        elif pv[-2:] in (['M', '`'], ['inl', '`']) or pv[-1:] == ['{'] or nx[:3] == ['e.', '(', '2nd']:
            pass
        else:
            raise ValueError('F0 in an unknown context: %s' % ' '.join(toks[max(0, i - 12):i + 12]))
    return out


def fix_line(l):
    if ' |- ' in l:
        head, f = l.split(' |- ', 1)
        f = ' '.join(handler_f0(f.split()))
    else:
        head, f = l, None
    parts = head.split(':')
    if len(parts) >= 3:
        parts[2] = RENAME.get(parts[2], parts[2])
    head = ':'.join(parts)
    return head if f is None else '%s |- %s' % (head, f)


class WG(tm.W):
    def __init__(self, label, desc):
        tm.W.__init__(self, RENAME.get(label, label),
                      desc + '  The pop handler of ` dup ` \'s ` move2Num ` is the class variable ` G ` .')

    def write(self):
        return tm.ws(self.label, self.desc, [fix_line(l) for l in self.lines])


import t6b_e_cpy as E
import tmd_a_cpyn as D
E.W = WG
D.W = WG

SEL = sys.argv[1:] or ['tm2lcpybg', 'tm2lcpylg', 'tm2lcpyg', 'tm2lcpyng', 'tm2lcpyb2g']
INV = {v: k for k, v in RENAME.items()}

if __name__ == '__main__':
    for l in SEL:
        src = INV[l]
        mod = E if hasattr(E, src) else D
        if not getattr(mod, src)():
            sys.exit(1)
