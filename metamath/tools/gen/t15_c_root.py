"""T15 (c, root): the root installation predicate and the concrete machine definitions (text for sorties/t15.mm)."""
import sys, re
sys.path.insert(0,'/Users/dan/carmichael/metamath/tools'); sys.path.insert(0,'/Users/dan/carmichael/metamath/tools/gen')
from t15lib import *
import t15lib
rhs, S = ROOT_RHS, ROOT_S0
from t15_c_defs import dline, fold
P = load_preds()
P['TMIroot'] = (['C','K','T','M','P','E'], rhs.split(), 'df-tmiroot')
t15lib.FAMPAR['TMIroot'] = ['C','K']
out = []
out.append('')
out.append('  $c TMIroot TMnroot TMFroot TMLbl TMTy TMRoot TMProg TMMach $.')
out.append('')
out.append('  $( Extend wff notation with the installation of the whole program. $)')
out.append('  wtmiroot $a wff TMIroot C K T M P E $.')
out.append('  $( The installation of the whole program (sortie T15): the prefix of route beta (copy the input with ~ df-tmiinp , duplicate it, push 16, compare, branch), the small-input answer ~ df-tmifal , the two move loops restoring the input, the search ~ df-tmisrch , and the exit that loads the initial state and halts.  The exit class ` E ` is not used. $)')
out.append('  ${\n    $d u C $.  $d u K $.  $d u T $.  $d u M $.  $d u P $.  $d u E $.\n    df-tmiroot $a |- ( TMIroot C K T M P E <-> %s ) $.\n  $}' % fold(rhs, '        '))
body, items = content_body('TMIroot', P)
text = '( TMnroot C K T P E ) = %s' % body
out.append('  $( Extend class notation with the content node of the whole program. $)')
out.append('  ctmnroot $a class ( TMnroot C K T P E ) $.')
out.append('  ${\n    %s\n    $( The program content of the whole program ( ~ df-tmiroot ). $)\n    df-tmnroot $a |- %s $.\n  $}' % (dline(text), fold(text)))
fsyn = '( TMFroot W C K )'
text = '%s = %s' % (fsyn, fam_body('TMIroot', P))
out.append('  $( Extend class notation with the label family of the whole program. $)')
out.append('  ctmfroot $a class ( TMFroot W C K ) $.')
out.append('  ${\n    %s\n    $( The label family of the whole program. $)\n    df-tmfroot $a |- %s $.\n  $}' % (dline(text), fold(text)))
A = '( 0 ... ( ( C + K ) + ; ; 1 0 1 ) )'
defs = [
 ('tmlbl', '( TMLbl C K )', '( TMLab " { w e. Word %s | ( # ` w ) <_ ; 3 0 } )' % A, 'The label set of the concrete machine: the address labels of depth at most 30 over the letters up to ` ( C + K ) + 101 ` .'),
 ('tmty', '( TMTy C K )', '<. <. TMGam , ( TMLbl C K ) >. , TMSt >.', 'The type triple of the concrete machine (Lean ` Gamma , Lambda , sigma ` ).'),
 ('tmroot', '( TMRoot C K )', '( TMnroot C K ( TMTy C K ) ( TMFroot (/) C K ) ( TMLab ` (/) ) )', 'The program trie of the concrete machine.'),
 ('tmprog', '( TMProg C K )', '( x e. ( TMLbl C K ) |-> if ( ( ( TMRoot C K ) TMWalk ( x ` -u 1 ) ) e. ( TM2Stmt ` ( TMTy C K ) ) , ( ( TMRoot C K ) TMWalk ( x ` -u 1 ) ) , <. 6 , (/) >. ) )', 'The program of the concrete machine: the statement found at the address of the label (Lean ` searchTM ` , MainProof.lean).'),
 ('tmmach', '( TMMach C K )', '<. <. ( TMTy C K ) , <. 0 , 1 >. >. , <. <. ( TMLab ` ( ( (/) ++ <" 0 "> ) ++ <" 0 "> ) ) , %s >. , ( TMProg C K ) >. >.' % S, 'The concrete machine as a ` FinTM2 ` tuple: input stack 0, output stack 1, the entry of the prefix, the initial state, the program.'),
]
for lab, lhs, rhs_, com in defs:
    out.append('  $( Extend class notation with %s. $)' % lhs)
    out.append('  c%s $a class %s $.' % (lab, lhs))
    text = '%s = %s' % (lhs, rhs_)
    dl = dline(text)
    out.append('  ${\n    %s\n    $( %s $)\n    df-%s $a |- %s $.\n  $}' % (dl, com, lab, fold(text)))
sys.stdout.write('\n'.join(out)+'\n')
