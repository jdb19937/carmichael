"""T7: T-MD's multiplication and division assemblies with the stack family that
shares its name with the terminator letter renamed.

In the merged ~ tm2fml the terminator pushed on the accumulator and the family
of the multiplier's stacks are both the class variable ` Y ` ; in ~ tm2fdmc2 ,
~ tm2fdmc , ~ tm2fdm , ~ tm2fdiv , ~ tm2fmod the terminator and the family of
the divisor's stacks of the shift-down loop are.  An instance must then take
` Y ` as the letter ` 4 ` and ` ( 4 ` i ) ` as the stacks: no concrete machine
satisfies those hypotheses.  This generator reruns T-MD's own proofs
(tools/gen/tmd_i_mul.py, tools/gen/tmd_o_dmc.py) with the family renamed
( ` Y' ` for the multiplier, ` Y" ` for the divisor; the shift-up loop keeps
its ` Y' ` ), under the labels ` tm2fmlv ` , ` tm2fdmc2v ` , ` tm2fdmcv ` ,
` tm2fdmv ` , ` tm2fdivv ` , ` tm2fmodv ` .  Each statement is the merged one
with ` ( Y ` ` replaced by ` ( Y' ` ` resp. ` ( Y" ` ` .

    MM_DB=sorties/t7.mm python3 tools/gen/t7_o_fml.py [ml] [dm LABEL...]
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import importlib
import tmdlib

HERE = os.path.dirname(os.path.abspath(__file__))
_SRC = open(os.path.join(HERE, '..', 'tmdlib.py')).read()


def patched(fam):
    """re-evaluate tmdlib's statement constants with the family ` Y ` named fam"""
    tmdlib.YF = lambda i: '( %s ` %s )' % (fam, i)
    exec(_SRC[_SRC.index('HYPS_MQ = '):_SRC.index('STATEMENTS = [')], tmdlib.__dict__)
    tmdlib.STATEMENTS = []
    exec(_SRC[_SRC.index('GIP = GX'):], tmdlib.__dict__)
    tmdlib.UPMAP[fam] = "Y'"
    exec(_SRC[_SRC.index('DPU_ = lambda i'):], tmdlib.__dict__)


def run_gen(fname, relabel, fam, sel):
    patched(fam)
    g = open(os.path.join(HERE, fname)).read()
    for a, b in relabel.items():
        g = g.replace("'%s'" % a, "'%s'" % b)
    pre = ('T-MD\'s statement with the stack family ` Y ` of the merged theorem renamed ` %s ` (the merged '
           'one names the terminator letter and that family alike, which no concrete machine satisfies).  ') % fam
    g = g.replace("w = W(lab, '", "w = W(lab, '" + pre.replace("'", "\\'"))
    ns = {'__name__': 't7_o_inner', '__file__': os.path.join(HERE, fname)}
    exec(g, ns)
    for lab in sel:
        ns[lab]()


ML = {'tm2fml': 'tm2fmlv'}
DM = {'tm2fdmc2': 'tm2fdmc2v', 'tm2fdmc': 'tm2fdmcv', 'tm2fdm': 'tm2fdmv', 'tm2fdiv': 'tm2fdivv', 'tm2fmod': 'tm2fmodv'}

if __name__ == '__main__':
    args = sys.argv[1:]
    if not args or args[0] == 'ml':
        run_gen('tmd_i_mul.py', ML, "Y'", ['tm2fml'])
    if not args or args[0] == 'dm':
        sel = args[1:] if len(args) > 1 else ['tm2fdmc2', 'tm2fdmc', 'tm2fdm', 'tm2fdiv', 'tm2fmod']
        run_gen('tmd_o_dmc.py', DM, 'Y"', sel)
