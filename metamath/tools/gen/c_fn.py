import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..')); from tm import *
T='T'; PRT=PR(T)
w = W('tm2safn', 'The depth-N function of the recursion of TM2sa is a function on the depth-N statements paired with (state, stacks).')
s1 = w.s([], 'tm2safnlem', '( N e. _om -> ( T e. V -> %s Fn ( %s X. %s ) ) )' % (FN(T,'N'), LYN(T,'N'), PRT))
w.qed([s1], 'impcom', '( ( T e. V /\\ N e. _om ) -> %s Fn ( %s X. %s ) )' % (FN(T,'N'), LYN(T,'N'), PRT))
w.run()
