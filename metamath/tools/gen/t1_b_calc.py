"""T1: the fragment calculus proper --- typing, weakening, composition,
case split, one step, iteration, and the conversion to TM2OutputsInTime."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t1lib import *
from lin import linarith

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

TV = '( T e. V /\\ M e. W )'
OP = OPAB('T', 'M')
PW = PWX('T')
OPN = '<. C , <. D , N >. >.'
CFGT = CFG('T')


def tm2hrtyp():
    lab = 'tm2hrtyp'
    ph = '( %s /\\ %s )' % (TV, HR('C', 'T', 'M', 'D', 'N'))
    w = W(lab, 'The typing a Hoare triple of the machine layer carries: both '
               'classes are classes of configurations and the step bound is a '
               'nonnegative integer.  Lean leaves this to its type '
               'ascriptions.')
    tv = w.s([], 'simpl', '( %s -> %s )' % (ph, TV))
    br = w.s([], 'simpr', '( %s -> %s )' % (ph, HR('C', 'T', 'M', 'D', 'N')))
    dbr = w.s([], 'df-br', '( %s <-> %s e. ( T TM2Hoare M ) )' % (HR('C', 'T', 'M', 'D', 'N'), OPN))
    el0 = w.s([br, dbr], 'sylib', '( %s -> %s e. ( T TM2Hoare M ) )' % (ph, OPN))
    val = w.s([tv, w.inst('tm2hrval')], 'syl', '( %s -> ( T TM2Hoare M ) = ( %s i^i %s ) )' % (ph, OP, PW))
    el1 = w.s([el0, val], 'eleqtrd', '( %s -> %s e. ( %s i^i %s ) )' % (ph, OPN, OP, PW))
    ei = w.s([], 'elin', '( %s e. ( %s i^i %s ) <-> ( %s e. %s /\\ %s e. %s ) )' % (OPN, OP, PW, OPN, OP, OPN, PW))
    el2 = w.s([el1, ei], 'sylib', '( %s -> ( %s e. %s /\\ %s e. %s ) )' % (ph, OPN, OP, OPN, PW))
    el3 = w.s([el2], 'simprd', '( %s -> %s e. %s )' % (ph, OPN, PW))
    x1 = w.s([], 'opelxp', '( %s e. %s <-> ( C e. ~P %s /\\ <. D , N >. e. ( ~P %s X. NN0 ) ) )'
             % (OPN, PW, CFGT, CFGT))
    el4 = w.s([el3, x1], 'sylib', '( %s -> ( C e. ~P %s /\\ <. D , N >. e. ( ~P %s X. NN0 ) ) )' % (ph, CFGT, CFGT))
    cp = w.s([el4], 'simpld', '( %s -> C e. ~P %s )' % (ph, CFGT))
    dp = w.s([el4], 'simprd', '( %s -> <. D , N >. e. ( ~P %s X. NN0 ) )' % (ph, CFGT))
    x2 = w.s([], 'opelxp', '( <. D , N >. e. ( ~P %s X. NN0 ) <-> ( D e. ~P %s /\\ N e. NN0 ) )' % (CFGT, CFGT))
    el5 = w.s([dp, x2], 'sylib', '( %s -> ( D e. ~P %s /\\ N e. NN0 ) )' % (ph, CFGT))
    dpw = w.s([el5], 'simpld', '( %s -> D e. ~P %s )' % (ph, CFGT))
    nn = w.s([el5], 'simprd', '( %s -> N e. NN0 )' % ph)
    cs = w.s([cp, w.inst('elpwi')], 'syl', '( %s -> C C_ %s )' % (ph, CFGT))
    ds = w.s([dpw, w.inst('elpwi')], 'syl', '( %s -> D C_ %s )' % (ph, CFGT))
    w.qed([cs, ds, nn], '3jca', '( %s -> %s )' % (ph, TYP('C', 'D', 'N', 'T')))
    return w.run()


def tm2hrbr2():
    lab = 'tm2hrbr2'
    ph = '( %s /\\ %s )' % (TV, TYP('C', 'D', 'N', 'T'))
    bodyF = BODY('T', 'M', 'C', 'D', 'N')
    w = W(lab, 'The Hoare triple of the machine layer under its typing: the '
               'form a fragment lemma introduces and eliminates.')
    tv = w.s([], 'simpl', '( %s -> %s )' % (ph, TV))
    cs = w.s([], 'simpr1', '( %s -> C C_ %s )' % (ph, CFGT))
    ds = w.s([], 'simpr2', '( %s -> D C_ %s )' % (ph, CFGT))
    nn = w.s([], 'simpr3', '( %s -> N e. NN0 )' % ph)
    ce = w.s([], 'fvex', '%s e. _V' % CFGT)
    cea = w.s([ce], 'a1i', '( %s -> %s e. _V )' % (ph, CFGT))
    cv = w.s([cs, cea], 'ssexd', '( %s -> C e. _V )' % ph)
    dv = w.s([ds, cea], 'ssexd', '( %s -> D e. _V )' % ph)
    nv = w.s([nn], 'elexd', '( %s -> N e. _V )' % ph)
    tri = w.s([cv, dv, nv], '3jca', '( %s -> ( C e. _V /\\ D e. _V /\\ N e. _V ) )' % ph)
    both = w.s([tv, tri], 'jca', '( %s -> ( %s /\\ ( C e. _V /\\ D e. _V /\\ N e. _V ) ) )' % (ph, TV))
    bi = w.s([both, w.inst('tm2hrbr')], 'syl',
             '( %s -> ( %s <-> ( %s /\\ %s ) ) )' % (ph, HR('C', 'T', 'M', 'D', 'N'), TYP('C', 'D', 'N', 'T'), bodyF))
    ty = w.s([cs, ds, nn], '3jca', '( %s -> %s )' % (ph, TYP('C', 'D', 'N', 'T')))
    ba = w.s([ty], 'biantrurd', '( %s -> ( %s <-> ( %s /\\ %s ) ) )' % (ph, bodyF, TYP('C', 'D', 'N', 'T'), bodyF))
    w.qed([bi, ba], 'bitr4d', '( %s -> ( %s <-> %s ) )' % (ph, HR('C', 'T', 'M', 'D', 'N'), bodyF))
    return w.run()






def tm2hmvv():
    w = W('tm2hmvv', 'The program of a machine is a set.')
    lv = w.s([], 'fvex', '%s e. _V' % L('T'))
    lva = w.s([lv], 'a1i', '( %s -> %s e. _V )' % (PHM, L('T')))
    mf = w.s([], 'simpr', '( %s -> M : %s --> %s )' % (PHM, L('T'), STMT('T')))
    w.qed([mf, lva, w.inst('fex')], 'syl2anc', '( %s -> M e. _V )' % PHM)
    return w.run()


def tm2hstf():
    w = W('tm2hstf', 'The optional-step function of a machine maps optional '
                     'configurations to optional configurations: the function '
                     'the Hoare triple iterates.')
    sf = w.s([], 'tm2stepf', '( %s -> ( T TM2step M ) : %s --> %s )' % (PHM, CFGT, OPTC('T')))
    ce = w.s([], 'fvex', '%s e. _V' % CFGT)
    cea = w.s([ce], 'a1i', '( %s -> %s e. _V )' % (PHM, CFGT))
    w.qed([cea, sf, w.inst('optstepf')], 'syl2anc',
          '( %s -> %s : %s --> %s )' % (PHM, OPS('T', 'M'), OPTC('T'), OPTC('T')))
    return w.run()


def tm2hsdm():
    w = W('tm2hsdm', 'The domain of the step function of a machine.')
    sf = w.s([], 'tm2stepf', '( %s -> ( T TM2step M ) : %s --> %s )' % (PHM, CFGT, OPTC('T')))
    w.qed([sf], 'fdmd', '( %s -> dom ( T TM2step M ) = %s )' % (PHM, CFGT))
    return w.run()


def tm2hid():
    lab = 'tm2hid'
    ph = '( %s /\\ C C_ %s )' % (PHM, CFGT)
    ph2 = '( %s /\\ u e. C )' % ph
    I0 = ITER('T', 'M', '0', '( inl ` u )')
    Ii = ITER('T', 'M', 'i', '( inl ` u )')
    body = BODY('T', 'M', 'C', 'C', '0')
    w = W(lab, 'Reflexivity of the Hoare triple of the machine layer: every '
               'class of configurations reaches itself in no steps.  Lean: '
               '` runsTo_zero ` .')
    cs = w.s([], 'simplr', '( %s -> C C_ %s )' % (ph2, CFGT))
    uc = w.s([], 'simpr', '( %s -> u e. C )' % ph2)
    ucf = w.s([cs, uc], 'sseldd', '( %s -> u e. %s )' % (ph2, CFGT))
    inl = w.s([ucf, w.inst('djulcl')], 'syl', '( %s -> ( inl ` u ) e. %s )' % (ph2, OPTC('T')))
    ce0 = w.s([], 'fvex', '%s e. _V' % CFGT)
    o1 = w.s([], '1oex', '1o e. _V')
    oe = w.s([ce0, o1, w.inst('djuex')], 'mp2an', '%s e. _V' % OPTC('T'))
    oea = w.s([oe], 'a1i', '( %s -> %s e. _V )' % (ph2, OPTC('T')))
    sfp = w.s([], 'simpll', '( %s -> %s )' % (ph2, PHM))
    sf = w.s([sfp, w.inst('tm2hstf')], 'syl',
             '( %s -> %s : %s --> %s )' % (ph2, OPS('T', 'M'), OPTC('T'), OPTC('T')))
    r0 = w.s([oea, sf, inl, w.inst('relexp0fv')], 'syl3anc', '( %s -> %s = ( inl ` u ) )' % (ph2, I0))
    # E. w e. C
    sw1 = w.s([], 'fveq2', '( w = u -> ( inl ` w ) = ( inl ` u ) )')
    sw2 = w.s([sw1], 'eqeq2d', '( w = u -> ( %s = ( inl ` w ) <-> %s = ( inl ` u ) ) )' % (I0, I0))
    ew = w.s([uc, r0, w.inst('rspcev')], 'syl2anc', '( %s -> E. w e. C %s = ( inl ` w ) )' % (ph2, I0))
    # E. i e. ( 0 ... 0 )
    si1 = w.s([], 'oveq2', '( i = 0 -> ( %s ^r i ) = ( %s ^r 0 ) )' % (OPS('T', 'M'), OPS('T', 'M')))
    si2 = w.s([si1], 'fveq1d', '( i = 0 -> %s = %s )' % (Ii, I0))
    si3 = w.s([si2], 'eqeq1d', '( i = 0 -> ( %s = ( inl ` w ) <-> %s = ( inl ` w ) ) )' % (Ii, I0))
    si4 = w.s([si3], 'rexbidv', '( i = 0 -> ( E. w e. C %s = ( inl ` w ) <-> E. w e. C %s = ( inl ` w ) ) )' % (Ii, I0))
    z0 = w.s([], '0nn0', '0 e. NN0')
    zf = w.s([], 'nn0fz0', '( 0 e. NN0 <-> 0 e. ( 0 ... 0 ) )')
    zfz = w.s([z0, zf], 'mpbi', '0 e. ( 0 ... 0 )')
    zfza = w.s([zfz], 'a1i', '( %s -> 0 e. ( 0 ... 0 ) )' % ph2)
    ei = w.s([zfza, ew, w.inst('rspcev')], 'syl2anc', '( %s -> E. i e. ( 0 ... 0 ) E. w e. C %s = ( inl ` w ) )' % (ph2, Ii))
    ral = w.s([ei], 'ralrimiva', '( %s -> %s )' % (ph, body))
    # typing and the triple
    css = w.s([], 'simpr', '( %s -> C C_ %s )' % (ph, CFGT))
    z0a = w.s([z0], 'a1i', '( %s -> 0 e. NN0 )' % ph)
    ty = w.s([css, css, z0a], '3jca', '( %s -> %s )' % (ph, TYP('C', 'C', '0', 'T')))
    phm = w.s([], 'simpl', '( %s -> %s )' % (ph, PHM))
    hrintro(w, ph, phm, 'C', 'C', '0', ty, ral, qed=True)
    return w.run()


def tm2hssc():
    lab = 'tm2hssc'
    pre = '( %s /\\ %s )' % (PHM, HR('C', 'T', 'M', 'D', 'N'))
    ph = '( %s /\\ S C_ C )' % pre
    w = W(lab, 'Shrinking the precondition of a Hoare triple of the machine '
               'layer.  Half of Lean\'s ` Frag.runs_mono ` .')
    phm = w.s([], 'simpll', '( %s -> %s )' % (ph, PHM))
    br = w.s([], 'simplr', '( %s -> %s )' % (ph, HR('C', 'T', 'M', 'D', 'N')))
    sc = w.s([], 'simpr', '( %s -> S C_ C )' % ph)
    ty, bd = hrelim(w, ph, phm, 'C', 'D', 'N', br)
    cs = w.s([ty], 'simp1d', '( %s -> C C_ %s )' % (ph, CFGT))
    ds = w.s([ty], 'simp2d', '( %s -> D C_ %s )' % (ph, CFGT))
    nn = w.s([ty], 'simp3d', '( %s -> N e. NN0 )' % ph)
    ss = w.s([sc, cs], 'sstrd', '( %s -> S C_ %s )' % (ph, CFGT))
    ty2 = w.s([ss, ds, nn], '3jca', '( %s -> %s )' % (ph, TYP('S', 'D', 'N', 'T')))
    imp = w.s([sc, w.inst('ssralv')], 'syl',
              '( %s -> ( %s -> %s ) )' % (ph, BODY('T', 'M', 'C', 'D', 'N'), BODY('T', 'M', 'S', 'D', 'N')))
    bd2 = w.s([imp, bd], 'mpd', '( %s -> %s )' % (ph, BODY('T', 'M', 'S', 'D', 'N')))
    hrintro(w, ph, phm, 'S', 'D', 'N', ty2, bd2, qed=True)
    return w.run()


def tm2hssd():
    lab = 'tm2hssd'
    pre = '( %s /\\ %s )' % (PHM, HR('C', 'T', 'M', 'D', 'N'))
    ph = '( %s /\\ ( D C_ R /\\ R C_ %s ) )' % (pre, CFGT)
    Iu = ITER('T', 'M', 'i', '( inl ` u )')
    EwD = 'E. w e. D %s = ( inl ` w )' % Iu
    EwR = 'E. w e. R %s = ( inl ` w )' % Iu
    EiD = 'E. i e. ( 0 ... N ) %s' % EwD
    EiR = 'E. i e. ( 0 ... N ) %s' % EwR
    w = W(lab, 'Growing the postcondition of a Hoare triple of the machine '
               'layer.  Half of Lean\'s ` Frag.runs_mono ` .')
    phm = w.s([], 'simpll', '( %s -> %s )' % (ph, PHM))
    br = w.s([], 'simplr', '( %s -> %s )' % (ph, HR('C', 'T', 'M', 'D', 'N')))
    dr = w.s([], 'simprl', '( %s -> D C_ R )' % ph)
    rs = w.s([], 'simprr', '( %s -> R C_ %s )' % (ph, CFGT))
    ty, bd = hrelim(w, ph, phm, 'C', 'D', 'N', br)
    cs = w.s([ty], 'simp1d', '( %s -> C C_ %s )' % (ph, CFGT))
    nn = w.s([ty], 'simp3d', '( %s -> N e. NN0 )' % ph)
    ty2 = w.s([cs, rs, nn], '3jca', '( %s -> %s )' % (ph, TYP('C', 'R', 'N', 'T')))
    i1 = w.s([dr, w.inst('ssrexv')], 'syl', '( %s -> ( %s -> %s ) )' % (ph, EwD, EwR))
    i2 = w.s([i1], 'adantr', '( ( %s /\\ i e. ( 0 ... N ) ) -> ( %s -> %s ) )' % (ph, EwD, EwR))
    i3 = w.s([i2], 'reximdva', '( %s -> ( %s -> %s ) )' % (ph, EiD, EiR))
    i4 = w.s([i3], 'adantr', '( ( %s /\\ u e. C ) -> ( %s -> %s ) )' % (ph, EiD, EiR))
    i5 = w.s([i4], 'ralimdva', '( %s -> ( %s -> %s ) )'
             % (ph, BODY('T', 'M', 'C', 'D', 'N'), BODY('T', 'M', 'C', 'R', 'N')))
    bd2 = w.s([i5, bd], 'mpd', '( %s -> %s )' % (ph, BODY('T', 'M', 'C', 'R', 'N')))
    hrintro(w, ph, phm, 'C', 'R', 'N', ty2, bd2, qed=True)
    return w.run()


def tm2hle():
    lab = 'tm2hle'
    pre = '( %s /\\ %s )' % (PHM, HR('C', 'T', 'M', 'D', 'N'))
    ph = '( %s /\\ ( P e. NN0 /\\ N <_ P ) )' % pre
    Iu = ITER('T', 'M', 'i', '( inl ` u )')
    Ew = 'E. w e. D %s = ( inl ` w )' % Iu
    EiN = 'E. i e. ( 0 ... N ) %s' % Ew
    EiP = 'E. i e. ( 0 ... P ) %s' % Ew
    w = W(lab, 'Raising the step bound of a Hoare triple of the machine layer.  '
               'Half of Lean\'s ` Frag.runs_mono ` ; the step counts of the '
               'machine layer are upper bounds throughout.')
    phm = w.s([], 'simpll', '( %s -> %s )' % (ph, PHM))
    br = w.s([], 'simplr', '( %s -> %s )' % (ph, HR('C', 'T', 'M', 'D', 'N')))
    pn = w.s([], 'simprl', '( %s -> P e. NN0 )' % ph)
    le = w.s([], 'simprr', '( %s -> N <_ P )' % ph)
    ty, bd = hrelim(w, ph, phm, 'C', 'D', 'N', br)
    cs = w.s([ty], 'simp1d', '( %s -> C C_ %s )' % (ph, CFGT))
    ds = w.s([ty], 'simp2d', '( %s -> D C_ %s )' % (ph, CFGT))
    nn = w.s([ty], 'simp3d', '( %s -> N e. NN0 )' % ph)
    ty2 = w.s([cs, ds, pn], '3jca', '( %s -> %s )' % (ph, TYP('C', 'D', 'P', 'T')))
    nz = w.s([nn], 'nn0zd', '( %s -> N e. ZZ )' % ph)
    pz = w.s([pn], 'nn0zd', '( %s -> P e. ZZ )' % ph)
    uz = w.s([nz, pz, le, w.inst('eluz2')], 'syl3anbrc', '( %s -> P e. ( ZZ>= ` N ) )' % ph)
    fs = w.s([uz, w.inst('fzss2')], 'syl', '( %s -> ( 0 ... N ) C_ ( 0 ... P ) )' % ph)
    i1 = w.s([fs, w.inst('ssrexv')], 'syl', '( %s -> ( %s -> %s ) )' % (ph, EiN, EiP))
    i2 = w.s([i1], 'adantr', '( ( %s /\\ u e. C ) -> ( %s -> %s ) )' % (ph, EiN, EiP))
    i3 = w.s([i2], 'ralimdva', '( %s -> ( %s -> %s ) )'
             % (ph, BODY('T', 'M', 'C', 'D', 'N'), BODY('T', 'M', 'C', 'D', 'P')))
    bd2 = w.s([i3, bd], 'mpd', '( %s -> %s )' % (ph, BODY('T', 'M', 'C', 'D', 'P')))
    hrintro(w, ph, phm, 'C', 'D', 'P', ty2, bd2, qed=True)
    return w.run()


def tm2hun():
    lab = 'tm2hun'
    ph = '( %s /\\ %s /\\ %s )' % (PHM, HR('C', 'T', 'M', 'D', 'N'), HR('S', 'T', 'M', 'D', 'N'))
    w = W(lab, 'A case split on the precondition of a Hoare triple of the '
               'machine layer: a branch statement sends the two halves of the '
               'precondition to the two branches, and this glues them.  Lean: '
               '` Frag.ite_runs ` .')
    phm = w.s([], 'simp1', '( %s -> %s )' % (ph, PHM))
    br1 = w.s([], 'simp2', '( %s -> %s )' % (ph, HR('C', 'T', 'M', 'D', 'N')))
    br2 = w.s([], 'simp3', '( %s -> %s )' % (ph, HR('S', 'T', 'M', 'D', 'N')))
    ty1, bd1 = hrelim(w, ph, phm, 'C', 'D', 'N', br1)
    ty2, bd2 = hrelim(w, ph, phm, 'S', 'D', 'N', br2)
    cs = w.s([ty1], 'simp1d', '( %s -> C C_ %s )' % (ph, CFGT))
    ds = w.s([ty1], 'simp2d', '( %s -> D C_ %s )' % (ph, CFGT))
    nn = w.s([ty1], 'simp3d', '( %s -> N e. NN0 )' % ph)
    ss = w.s([ty2], 'simp1d', '( %s -> S C_ %s )' % (ph, CFGT))
    us = w.s([cs, ss], 'unssd', '( %s -> ( C u. S ) C_ %s )' % (ph, CFGT))
    ty = w.s([us, ds, nn], '3jca', '( %s -> %s )' % (ph, TYP('( C u. S )', 'D', 'N', 'T')))
    both = w.s([bd1, bd2], 'jca', '( %s -> ( %s /\\ %s ) )'
               % (ph, BODY('T', 'M', 'C', 'D', 'N'), BODY('T', 'M', 'S', 'D', 'N')))
    ru = w.s([], 'ralunb', '( %s <-> ( %s /\\ %s ) )'
             % (BODY('T', 'M', '( C u. S )', 'D', 'N'), BODY('T', 'M', 'C', 'D', 'N'), BODY('T', 'M', 'S', 'D', 'N')))
    rua = w.s([ru], 'a1i', '( %s -> ( %s <-> ( %s /\\ %s ) ) )'
              % (ph, BODY('T', 'M', '( C u. S )', 'D', 'N'), BODY('T', 'M', 'C', 'D', 'N'), BODY('T', 'M', 'S', 'D', 'N')))
    bd = w.s([rua, both], 'mpbird', '( %s -> %s )' % (ph, BODY('T', 'M', '( C u. S )', 'D', 'N')))
    hrintro(w, ph, phm, '( C u. S )', 'D', 'N', ty, bd, qed=True)
    return w.run()


def tm2hseq():
    lab = 'tm2hseq'
    ph = '( %s /\\ %s /\\ %s )' % (PHM, HR('C', 'T', 'M', 'D', 'N'), HR('D', 'T', 'M', 'R', 'P'))
    ps = '( %s /\\ u e. C )' % ph
    lv1 = '( %s /\\ a e. ( 0 ... N ) )' % ps
    lv2 = '( %s /\\ b e. D )' % lv1
    Ea = ITER('T', 'M', 'a', '( inl ` u )')
    Ec = ITER('T', 'M', 'c', '( inl ` b )')
    Eca = ITER('T', 'M', '( c + a )', '( inl ` u )')
    Ei = ITER('T', 'M', 'i', '( inl ` u )')
    lv3 = '( %s /\\ %s = ( inl ` b ) )' % (lv2, Ea)
    lv4 = '( %s /\\ c e. ( 0 ... P ) )' % lv3
    lv5 = '( %s /\\ d e. R )' % lv4
    lv6 = '( %s /\\ %s = ( inl ` d ) )' % (lv5, Ec)
    GOAL = 'E. i e. ( 0 ... ( N + P ) ) E. w e. R %s = ( inl ` w )' % Ei
    EwR = 'E. w e. R %s = ( inl ` w )' % Eca
    G = OPS('T', 'M')
    OC = OPTC('T')
    w = W(lab, 'Sequential composition of Hoare triples of the machine layer: '
               'the step bounds add.  Lean: ` Frag.seq_runs ` with '
               '` runsTo_trans ` , where the intermediate configurations are '
               'the universally quantified hypothesis '
               '` forall v S, Q1 v S -> G.Runs v S Q2 t2 ` ; here they are the '
               'class ` D ` and no quantifier appears.')
    phm = w.s([], 'simp1', '( %s -> %s )' % (ph, PHM))
    br1 = w.s([], 'simp2', '( %s -> %s )' % (ph, HR('C', 'T', 'M', 'D', 'N')))
    br2 = w.s([], 'simp3', '( %s -> %s )' % (ph, HR('D', 'T', 'M', 'R', 'P')))
    ty1, bd1 = hrelim(w, ph, phm, 'C', 'D', 'N', br1)
    ty2, bd2 = hrelim(w, ph, phm, 'D', 'R', 'P', br2)
    cs = w.s([ty1], 'simp1d', '( %s -> C C_ %s )' % (ph, CFGT))
    nn = w.s([ty1], 'simp3d', '( %s -> N e. NN0 )' % ph)
    rs = w.s([ty2], 'simp2d', '( %s -> R C_ %s )' % (ph, CFGT))
    pp = w.s([ty2], 'simp3d', '( %s -> P e. NN0 )' % ph)
    npn = w.s([nn, pp], 'nn0addcld', '( %s -> ( N + P ) e. NN0 )' % ph)
    ty = w.s([cs, rs, npn], '3jca', '( %s -> %s )' % (ph, TYP('C', 'R', '( N + P )', 'T')))
    r1, o1 = rename_body(w, ph, bd1, 'C', 'D', 'N', 'u', 'a', 'b')
    r2, o2 = rename_body(w, ph, bd2, 'D', 'R', 'P', 'b', 'c', 'd')
    # ---- the innermost level
    ucf = w.s([], 'simplr', '( %s -> u e. C )' % lv1)
    ucf6 = w.s([], 'simp-7r', '( %s -> u e. C )' % lv6)
    cs6 = w.s([cs], 'ad6antr', '( %s -> C C_ %s )' % (lv5, CFGT))
    cs6b = w.s([cs6], 'adantr', '( %s -> C C_ %s )' % (lv6, CFGT))
    ucfg = w.s([cs6b, ucf6], 'sseldd', '( %s -> u e. %s )' % (lv6, CFGT))
    inlu = w.s([ucfg, w.inst('djulcl')], 'syl', '( %s -> ( inl ` u ) e. %s )' % (lv6, OC))
    ce0 = w.s([], 'fvex', '%s e. _V' % CFGT)
    o1e = w.s([], '1oex', '1o e. _V')
    oe = w.s([ce0, o1e, w.inst('djuex')], 'mp2an', '%s e. _V' % OC)
    oea = w.s([oe], 'a1i', '( %s -> %s e. _V )' % (lv6, OC))
    phm6 = w.s([phm], 'ad7antr', '( %s -> %s )' % (lv6, PHM))
    sf = w.s([phm6, w.inst('tm2hstf')], 'syl', '( %s -> %s : %s --> %s )' % (lv6, G, OC, OC))
    afz = w.s([], 'simp-6r', '( %s -> a e. ( 0 ... N ) )' % lv6)
    cfz = w.s([], 'simpllr', '( %s -> c e. ( 0 ... P ) )' % lv6)
    an0 = w.s([afz, w.inst('elfz2nn0')], 'sylib', '( %s -> ( a e. NN0 /\\ N e. NN0 /\\ a <_ N ) )' % lv6)
    cn0 = w.s([cfz, w.inst('elfz2nn0')], 'sylib', '( %s -> ( c e. NN0 /\\ P e. NN0 /\\ c <_ P ) )' % lv6)
    aa = w.s([an0], 'simp1d', '( %s -> a e. NN0 )' % lv6)
    aN = w.s([an0], 'simp2d', '( %s -> N e. NN0 )' % lv6)
    aLe = w.s([an0], 'simp3d', '( %s -> a <_ N )' % lv6)
    cc = w.s([cn0], 'simp1d', '( %s -> c e. NN0 )' % lv6)
    cP = w.s([cn0], 'simp2d', '( %s -> P e. NN0 )' % lv6)
    cLe = w.s([cn0], 'simp3d', '( %s -> c <_ P )' % lv6)
    ocl = w.s([oea, sf], 'jca', '( %s -> ( %s e. _V /\\ %s : %s --> %s ) )' % (lv6, OC, G, OC, OC))
    cav = w.s([cc, aa], 'jca', '( %s -> ( c e. NN0 /\\ a e. NN0 ) )' % lv6)
    radd = w.s([ocl, cav, inlu, w.inst('relexpaddfv')], 'syl3anc',
               '( %s -> %s = ( ( %s ^r c ) ` %s ) )' % (lv6, Eca, G, Ea))
    st1 = w.s([], 'simp-4r', '( %s -> %s = ( inl ` b ) )' % (lv6, Ea))
    st2 = w.s([st1], 'fveq2d', '( %s -> ( ( %s ^r c ) ` %s ) = ( ( %s ^r c ) ` ( inl ` b ) ) )' % (lv6, G, Ea, G))
    st3 = w.s([], 'simpr', '( %s -> %s = ( inl ` d ) )' % (lv6, Ec))
    ch1 = w.s([radd, st2], 'eqtrd', '( %s -> %s = ( ( %s ^r c ) ` ( inl ` b ) ) )' % (lv6, Eca, G))
    ch2 = w.s([ch1, st3], 'eqtrd', '( %s -> %s = ( inl ` d ) )' % (lv6, Eca))
    dR = w.s([], 'simplr', '( %s -> d e. R )' % lv6)
    sw1 = w.s([], 'fveq2', '( w = d -> ( inl ` w ) = ( inl ` d ) )')
    sw2 = w.s([sw1], 'eqeq2d', '( w = d -> ( %s = ( inl ` w ) <-> %s = ( inl ` d ) ) )' % (Eca, Eca))
    ew = w.s([dR, ch2, w.inst('rspcev')], 'syl2anc', '( %s -> %s )' % (lv6, EwR))
    caN = w.s([cc, aa], 'nn0addcld', '( %s -> ( c + a ) e. NN0 )' % lv6)
    npn6 = w.s([aN, cP], 'nn0addcld', '( %s -> ( N + P ) e. NN0 )' % lv6)
    cr = w.s([cc], 'nn0red', '( %s -> c e. RR )' % lv6)
    ar = w.s([aa], 'nn0red', '( %s -> a e. RR )' % lv6)
    pr = w.s([cP], 'nn0red', '( %s -> P e. RR )' % lv6)
    nr = w.s([aN], 'nn0red', '( %s -> N e. RR )' % lv6)
    le2 = linarith(w, lv6, [cLe, aLe], '( c + a ) <_ ( N + P )',
                   leaves={'c': cr, 'a': ar, 'P': pr, 'N': nr})
    fz = w.s([caN, npn6, le2, w.inst('elfz2nn0')], 'syl3anbrc',
             '( %s -> ( c + a ) e. ( 0 ... ( N + P ) ) )' % lv6)
    si1 = w.s([], 'oveq2', '( i = ( c + a ) -> ( %s ^r i ) = ( %s ^r ( c + a ) ) )' % (G, G))
    si2 = w.s([si1], 'fveq1d', '( i = ( c + a ) -> %s = %s )' % (Ei, Eca))
    si3 = w.s([si2], 'eqeq1d', '( i = ( c + a ) -> ( %s = ( inl ` w ) <-> %s = ( inl ` w ) ) )' % (Ei, Eca))
    si4 = w.s([si3], 'rexbidv', '( i = ( c + a ) -> ( E. w e. R %s = ( inl ` w ) <-> %s ) )' % (Ei, EwR))
    g6 = w.s([fz, ew, w.inst('rspcev')], 'syl2anc', '( %s -> %s )' % (lv6, GOAL))
    # ---- peel d and c
    x5 = w.s([g6], 'ex', '( %s -> ( %s = ( inl ` d ) -> %s ) )' % (lv5, Ec, GOAL))
    x4 = w.s([x5], 'rexlimdva', '( %s -> ( E. d e. R %s = ( inl ` d ) -> %s ) )' % (lv4, Ec, GOAL))
    x3 = w.s([x4], 'rexlimdva',
             '( %s -> ( E. c e. ( 0 ... P ) E. d e. R %s = ( inl ` d ) -> %s ) )' % (lv3, Ec, GOAL))
    r2l = w.s([r2], 'ad4antr', '( %s -> %s )' % (lv3, o2))
    bD3 = w.s([], 'simplr', '( %s -> b e. D )' % lv3)
    inst2 = w.s([r2l, bD3, w.inst('rspa')], 'syl2anc',
                '( %s -> E. c e. ( 0 ... P ) E. d e. R %s = ( inl ` d ) )' % (lv3, Ec))
    g3 = w.s([x3, inst2], 'mpd', '( %s -> %s )' % (lv3, GOAL))
    # ---- peel b and a
    x2 = w.s([g3], 'ex', '( %s -> ( %s = ( inl ` b ) -> %s ) )' % (lv2, Ea, GOAL))
    x1 = w.s([x2], 'rexlimdva', '( %s -> ( E. b e. D %s = ( inl ` b ) -> %s ) )' % (lv1, Ea, GOAL))
    x0 = w.s([x1], 'rexlimdva',
             '( %s -> ( E. a e. ( 0 ... N ) E. b e. D %s = ( inl ` b ) -> %s ) )' % (ps, Ea, GOAL))
    r1l = w.s([r1], 'adantr', '( %s -> %s )' % (ps, o1))
    uC = w.s([], 'simpr', '( %s -> u e. C )' % ps)
    inst1 = w.s([r1l, uC, w.inst('rspa')], 'syl2anc',
                '( %s -> E. a e. ( 0 ... N ) E. b e. D %s = ( inl ` b ) )' % (ps, Ea))
    gps = w.s([x0, inst1], 'mpd', '( %s -> %s )' % (ps, GOAL))
    bd = w.s([gps], 'ralrimiva', '( %s -> %s )' % (ph, BODY('T', 'M', 'C', 'R', '( N + P )')))
    hrintro(w, ph, phm, 'C', 'R', '( N + P )', ty, bd, qed=True)
    return w.run()


def tm2hsa1():
    lab = 'tm2hsa1'
    ST = '( %s X. %s )' % (S('T'), STK('T'))
    ph = '( ( T e. V /\\ M e. W ) /\\ ( A e. %s /\\ U e. %s ) )' % (L('T'), ST)
    PU = '<. ( 1st ` U ) , ( 2nd ` U ) >.'
    w = W(lab, 'One step of a machine from a labelled configuration whose '
               'state-and-stacks part is not given as an explicit pair.  Lean: '
               '` step_label ` .')
    tv = w.s([], 'simpl', '( %s -> ( T e. V /\\ M e. W ) )' % ph)
    al = w.s([], 'simprl', '( %s -> A e. %s )' % (ph, L('T')))
    up = w.s([], 'simprr', '( %s -> U e. %s )' % (ph, ST))
    u12 = w.s([up, w.inst('1st2nd2')], 'syl', '( %s -> U = %s )' % (ph, PU))
    f1 = w.s([up, w.inst('xp1st')], 'syl', '( %s -> ( 1st ` U ) e. %s )' % (ph, S('T')))
    f2 = w.s([up, w.inst('xp2nd')], 'syl', '( %s -> ( 2nd ` U ) e. %s )' % (ph, STK('T')))
    j1 = w.s([f1, f2], 'jca', '( %s -> ( ( 1st ` U ) e. %s /\\ ( 2nd ` U ) e. %s ) )' % (ph, S('T'), STK('T')))
    j2 = w.s([al, j1], 'jca', '( %s -> ( A e. %s /\\ ( ( 1st ` U ) e. %s /\\ ( 2nd ` U ) e. %s ) ) )'
              % (ph, L('T'), S('T'), STK('T')))
    ts = w.s([tv, j2, w.inst('tm2stepsome')], 'syl2anc',
             '( %s -> ( ( T TM2step M ) ` <. ( inl ` A ) , %s >. ) = ( inl ` ( ( M ` A ) ( TM2sa ` T ) %s ) ) )'
             % (ph, PU, PU))
    o1 = w.s([u12], 'opeq2d', '( %s -> <. ( inl ` A ) , U >. = <. ( inl ` A ) , %s >. )' % (ph, PU))
    o2 = w.s([o1], 'fveq2d',
             '( %s -> ( ( T TM2step M ) ` <. ( inl ` A ) , U >. ) = ( ( T TM2step M ) ` <. ( inl ` A ) , %s >. ) )'
             % (ph, PU))
    o3 = w.s([u12], 'oveq2d', '( %s -> ( ( M ` A ) ( TM2sa ` T ) U ) = ( ( M ` A ) ( TM2sa ` T ) %s ) )' % (ph, PU))
    o4 = w.s([o3], 'fveq2d',
             '( %s -> ( inl ` ( ( M ` A ) ( TM2sa ` T ) U ) ) = ( inl ` ( ( M ` A ) ( TM2sa ` T ) %s ) ) )' % (ph, PU))
    o5 = w.s([o2, ts], 'eqtrd',
             '( %s -> ( ( T TM2step M ) ` <. ( inl ` A ) , U >. ) = ( inl ` ( ( M ` A ) ( TM2sa ` T ) %s ) ) )' % (ph, PU))
    w.qed([o5, o4], 'eqtr4d',
          '( %s -> ( ( T TM2step M ) ` <. ( inl ` A ) , U >. ) = ( inl ` ( ( M ` A ) ( TM2sa ` T ) U ) ) )' % ph)
    return w.run()


def tm2hcfgss():
    lab = 'tm2hcfgss'
    ST = '( %s X. %s )' % (S('T'), STK('T'))
    ph = '( T e. V /\\ A e. %s /\\ P C_ %s )' % (L('T'), ST)
    w = W(lab, 'The configurations at a given label with state-and-stacks in a '
               'given class are configurations.')
    tv = w.s([], 'simp1', '( %s -> T e. V )' % ph)
    al = w.s([], 'simp2', '( %s -> A e. %s )' % (ph, L('T')))
    ps = w.s([], 'simp3', '( %s -> P C_ %s )' % (ph, ST))
    dj = w.s([al, w.inst('djulcl')], 'syl', '( %s -> ( inl ` A ) e. %s )' % (ph, '( %s |_| 1o )' % L('T')))
    sn = w.s([dj], 'snssd', '( %s -> { ( inl ` A ) } C_ %s )' % (ph, '( %s |_| 1o )' % L('T')))
    xs = w.s([sn, ps, w.inst('xpss12')], 'syl2anc', '( %s -> ( { ( inl ` A ) } X. P ) C_ ( %s X. %s ) )'
             % (ph, '( %s |_| 1o )' % L('T'), ST))
    cv = w.s([tv, w.inst('tm2cfgval')], 'syl', '( %s -> %s = ( %s X. %s ) )'
             % (ph, CFGT, '( %s |_| 1o )' % L('T'), ST))
    w.qed([xs, cv], 'sseqtrrd', '( %s -> ( { ( inl ` A ) } X. P ) C_ %s )' % (ph, CFGT))
    return w.run()


def tm2hstep():
    lab = 'tm2hstep'
    ST = '( %s X. %s )' % (S('T'), STK('T'))
    ph0 = '( %s /\\ ( A e. %s /\\ P C_ %s /\\ D C_ %s ) )' % (PHM, L('T'), ST, CFGT)
    COND = 'A. a e. P ( ( M ` A ) ( TM2sa ` T ) a ) e. D'
    ph = '( %s /\\ %s )' % (ph0, COND)
    CC = '( { ( inl ` A ) } X. P )'
    ps = '( %s /\\ u e. %s )' % (ph, CC)
    G = OPS('T', 'M')
    OC = OPTC('T')
    WW = '( ( M ` A ) ( TM2sa ` T ) ( 2nd ` u ) )'
    X = '( inl ` u )'
    I1 = ITER('T', 'M', '1', X)
    Ii = ITER('T', 'M', 'i', X)
    GOAL = 'E. i e. ( 0 ... 1 ) E. w e. D %s = ( inl ` w )' % Ii
    w = W(lab, 'One machine step as a Hoare triple: from the configurations at '
               'label ` A ` whose state-and-stacks part lies in ` P ` , the '
               'machine reaches in one step the configurations of ` D ` , '
               'provided the value of ` stepAux ` on the statement at ` A ` '
               'lies in ` D ` for every such part.  The only rule of the '
               'calculus that touches the machine model; the seven equation '
               'lemmas ~ tm2sahalt through ~ tm2sapop compute its hypothesis.  '
               'Lean: ` step_label ` with ` runsTo_succ ` .')
    phm = w.s([], 'simplll' if False else 'simpll', '( %s -> %s )' % (ph, PHM))
    al = w.s([], 'simplr1', '( %s -> A e. %s )' % (ph, L('T')))
    pss = w.s([], 'simplr2', '( %s -> P C_ %s )' % (ph, ST))
    dss = w.s([], 'simplr3', '( %s -> D C_ %s )' % (ph, CFGT))
    cond = w.s([], 'simpr', '( %s -> %s )' % (ph, COND))
    tvv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    cssph = w.s([tvv, al, pss, w.inst('tm2hcfgss')], 'syl3anc', '( %s -> %s C_ %s )' % (ph, CC, CFGT))
    # ---- inside the u scope
    uc = w.s([], 'simpr', '( %s -> u e. %s )' % (ps, CC))
    u2 = w.s([uc, w.inst('xp2nd')], 'syl', '( %s -> ( 2nd ` u ) e. P )' % ps)
    u1 = w.s([uc, w.inst('xp1st')], 'syl', '( %s -> ( 1st ` u ) e. { ( inl ` A ) } )' % ps)
    u1e = w.s([u1, w.inst('elsni')], 'syl', '( %s -> ( 1st ` u ) = ( inl ` A ) )' % ps)
    u12 = w.s([uc, w.inst('1st2nd2')], 'syl', '( %s -> u = <. ( 1st ` u ) , ( 2nd ` u ) >. )' % ps)
    u1o = w.s([u1e], 'opeq1d', '( %s -> <. ( 1st ` u ) , ( 2nd ` u ) >. = <. ( inl ` A ) , ( 2nd ` u ) >. )' % ps)
    u12b = w.s([u12, u1o], 'eqtrd', '( %s -> u = <. ( inl ` A ) , ( 2nd ` u ) >. )' % ps)
    sb1 = w.s([], 'oveq2', '( a = ( 2nd ` u ) -> ( ( M ` A ) ( TM2sa ` T ) a ) = %s )' % WW)
    sb2 = w.s([sb1], 'eleq1d', '( a = ( 2nd ` u ) -> ( ( ( M ` A ) ( TM2sa ` T ) a ) e. D <-> %s e. D ) )' % WW)
    conds = w.s([cond], 'adantr', '( %s -> %s )' % (ps, COND))
    wD = w.s([sb2, conds, u2], 'rspcdva', '( %s -> %s e. D )' % (ps, WW))
    css = w.s([cssph], 'adantr', '( %s -> %s C_ %s )' % (ps, CC, CFGT))
    ucfg = w.s([css, uc], 'sseldd', '( %s -> u e. %s )' % (ps, CFGT))
    inlu = w.s([ucfg, w.inst('djulcl')], 'syl', '( %s -> %s e. %s )' % (ps, X, OC))
    phms = w.s([phm], 'adantr', '( %s -> %s )' % (ps, PHM))
    dm = w.s([phms, w.inst('tm2hsdm')], 'syl', '( %s -> dom ( T TM2step M ) = %s )' % (ps, CFGT))
    udm = w.s([ucfg, dm], 'eleqtrrd', '( %s -> u e. dom ( T TM2step M ) )' % ps)
    sve = w.s([], 'ovex', '( T TM2step M ) e. _V')
    svea = w.s([sve], 'a1i', '( %s -> ( T TM2step M ) e. _V )' % ps)
    os = w.s([svea, udm, w.inst('optstepsome')], 'syl2anc',
             '( %s -> ( %s ` %s ) = ( ( T TM2step M ) ` u ) )' % (ps, G, X))
    sa = w.s([u12b], 'fveq2d',
             '( %s -> ( ( T TM2step M ) ` u ) = ( ( T TM2step M ) ` <. ( inl ` A ) , ( 2nd ` u ) >. ) )' % ps)
    psss = w.s([pss], 'adantr', '( %s -> P C_ %s )' % (ps, ST))
    u2st = w.s([psss, u2], 'sseldd', '( %s -> ( 2nd ` u ) e. %s )' % (ps, ST))
    tvs = w.s([tvv], 'adantr', '( %s -> T e. V )' % ps)
    mvs = w.s([phms, w.inst('tm2hmvv')], 'syl', '( %s -> M e. _V )' % ps)
    tvj = w.s([tvs, mvs], 'jca', '( %s -> ( T e. V /\\ M e. _V ) )' % ps)
    als = w.s([al], 'adantr', '( %s -> A e. %s )' % (ps, L('T')))
    alj = w.s([als, u2st], 'jca', '( %s -> ( A e. %s /\\ ( 2nd ` u ) e. %s ) )' % (ps, L('T'), ST))
    sa2 = w.s([tvj, alj, w.inst('tm2hsa1')], 'syl2anc',
              '( %s -> ( ( T TM2step M ) ` <. ( inl ` A ) , ( 2nd ` u ) >. ) = ( inl ` %s ) )' % (ps, WW))
    ch1 = w.s([os, sa], 'eqtrd', '( %s -> ( %s ` %s ) = ( ( T TM2step M ) ` <. ( inl ` A ) , ( 2nd ` u ) >. ) )' % (ps, G, X))
    ch2 = w.s([ch1, sa2], 'eqtrd', '( %s -> ( %s ` %s ) = ( inl ` %s ) )' % (ps, G, X, WW))
    # the iterate at 1
    ce0 = w.s([], 'fvex', '%s e. _V' % CFGT)
    o1e = w.s([], '1oex', '1o e. _V')
    oe = w.s([ce0, o1e, w.inst('djuex')], 'mp2an', '%s e. _V' % OC)
    oea = w.s([oe], 'a1i', '( %s -> %s e. _V )' % (ps, OC))
    sf = w.s([phms, w.inst('tm2hstf')], 'syl', '( %s -> %s : %s --> %s )' % (ps, G, OC, OC))
    z0 = w.s([], '0nn0', '0 e. NN0')
    z0a = w.s([z0], 'a1i', '( %s -> 0 e. NN0 )' % ps)
    ocl = w.s([oea, sf], 'jca', '( %s -> ( %s e. _V /\\ %s : %s --> %s ) )' % (ps, OC, G, OC, OC))
    rs = w.s([ocl, z0a, inlu, w.inst('relexpsucfv2')], 'syl3anc',
             '( %s -> ( ( %s ^r ( 0 + 1 ) ) ` %s ) = ( ( %s ^r 0 ) ` ( %s ` %s ) ) )' % (ps, G, X, G, G, X))
    gx = w.s([sf, inlu], 'ffvelcdmd', '( %s -> ( %s ` %s ) e. %s )' % (ps, G, X, OC))
    r0 = w.s([oea, sf, gx, w.inst('relexp0fv')], 'syl3anc',
             '( %s -> ( ( %s ^r 0 ) ` ( %s ` %s ) ) = ( %s ` %s ) )' % (ps, G, G, X, G, X))
    p01 = w.s([], '0p1e1', '( 0 + 1 ) = 1')
    p01a = w.s([p01], 'a1i', '( %s -> ( 0 + 1 ) = 1 )' % ps)
    q1 = w.s([p01a], 'oveq2d', '( %s -> ( %s ^r ( 0 + 1 ) ) = ( %s ^r 1 ) )' % (ps, G, G))
    q2 = w.s([q1], 'fveq1d', '( %s -> ( ( %s ^r ( 0 + 1 ) ) ` %s ) = %s )' % (ps, G, X, I1))
    it1 = w.s([q2, rs], 'eqtr3d', '( %s -> %s = ( ( %s ^r 0 ) ` ( %s ` %s ) ) )' % (ps, I1, G, G, X))
    it2 = w.s([it1, r0], 'eqtrd', '( %s -> %s = ( %s ` %s ) )' % (ps, I1, G, X))
    eqf = w.s([it2, ch2], 'eqtrd', '( %s -> %s = ( inl ` %s ) )' % (ps, I1, WW))
    sw1 = w.s([], 'fveq2', '( w = %s -> ( inl ` w ) = ( inl ` %s ) )' % (WW, WW))
    sw2 = w.s([sw1], 'eqeq2d', '( w = %s -> ( %s = ( inl ` w ) <-> %s = ( inl ` %s ) ) )' % (WW, I1, I1, WW))
    ew = w.s([wD, eqf, w.inst('rspcev')], 'syl2anc', '( %s -> E. w e. D %s = ( inl ` w ) )' % (ps, I1))
    si1 = w.s([], 'oveq2', '( i = 1 -> ( %s ^r i ) = ( %s ^r 1 ) )' % (G, G))
    si2 = w.s([si1], 'fveq1d', '( i = 1 -> %s = %s )' % (Ii, I1))
    si3 = w.s([si2], 'eqeq1d', '( i = 1 -> ( %s = ( inl ` w ) <-> %s = ( inl ` w ) ) )' % (Ii, I1))
    si4 = w.s([si3], 'rexbidv', '( i = 1 -> ( E. w e. D %s = ( inl ` w ) <-> E. w e. D %s = ( inl ` w ) ) )' % (Ii, I1))
    n1 = w.s([], '1nn0', '1 e. NN0')
    nf = w.s([], 'nn0fz0', '( 1 e. NN0 <-> 1 e. ( 0 ... 1 ) )')
    n1f = w.s([n1, nf], 'mpbi', '1 e. ( 0 ... 1 )')
    n1fa = w.s([n1f], 'a1i', '( %s -> 1 e. ( 0 ... 1 ) )' % ps)
    gg = w.s([n1fa, ew, w.inst('rspcev')], 'syl2anc', '( %s -> %s )' % (ps, GOAL))
    bd = w.s([gg], 'ralrimiva', '( %s -> %s )' % (ph, BODY('T', 'M', CC, 'D', '1')))
    n1a = w.s([n1], 'a1i', '( %s -> 1 e. NN0 )' % ph)
    ty = w.s([cssph, dss, n1a], '3jca', '( %s -> %s )' % (ph, TYP(CC, 'D', '1', 'T')))
    hrintro(w, ph, phm, CC, 'D', '1', ty, bd, qed=True)
    return w.run()


def tm2hcfgsr():
    lab = 'tm2hcfgsr'
    ST = '( %s X. %s )' % (S('T'), STK('T'))
    ph = '( T e. V /\\ P C_ %s )' % ST
    w = W(lab, 'The halted configurations with state-and-stacks in a given '
               'class are configurations.')
    tv = w.s([], 'simpl', '( %s -> T e. V )' % ph)
    ps = w.s([], 'simpr', '( %s -> P C_ %s )' % (ph, ST))
    z0 = w.s([], '0lt1o', '(/) e. 1o')
    dj = w.s([z0, w.inst('djurcl')], 'ax-mp', '( inr ` (/) ) e. ( %s |_| 1o )' % L('T'))
    dja = w.s([dj], 'a1i', '( %s -> ( inr ` (/) ) e. ( %s |_| 1o ) )' % (ph, L('T')))
    sn = w.s([dja], 'snssd', '( %s -> { ( inr ` (/) ) } C_ ( %s |_| 1o ) )' % (ph, L('T')))
    xs = w.s([sn, ps, w.inst('xpss12')], 'syl2anc',
             '( %s -> ( { ( inr ` (/) ) } X. P ) C_ ( ( %s |_| 1o ) X. %s ) )' % (ph, L('T'), ST))
    cv = w.s([tv, w.inst('tm2cfgval')], 'syl', '( %s -> %s = ( ( %s |_| 1o ) X. %s ) )' % (ph, CFGT, L('T'), ST))
    w.qed([xs, cv], 'sseqtrrd', '( %s -> ( { ( inr ` (/) ) } X. P ) C_ %s )' % (ph, CFGT))
    return w.run()


def inlinj():
    lab = 'inlinj'
    ph = '( A e. V /\\ B e. W )'
    w = W(lab, 'The left injection of a disjoint union is one-to-one.  Lean: '
               '` Option.some_injective ` .')
    av = w.s([], 'simpl', '( %s -> A e. V )' % ph)
    bv = w.s([], 'simpr', '( %s -> B e. W )' % ph)
    a1 = w.s([av, w.inst('inlval')], 'syl', '( %s -> ( inl ` A ) = <. (/) , A >. )' % ph)
    b1 = w.s([bv, w.inst('inlval')], 'syl', '( %s -> ( inl ` B ) = <. (/) , B >. )' % ph)
    e1 = w.s([a1, b1], 'eqeq12d', '( %s -> ( ( inl ` A ) = ( inl ` B ) <-> <. (/) , A >. = <. (/) , B >. ) )' % ph)
    z0 = w.s([], '0ex', '(/) e. _V')
    z0a = w.s([z0], 'a1i', '( %s -> (/) e. _V )' % ph)
    o1 = w.s([z0a, av, w.inst('opthg')], 'syl2anc',
             '( %s -> ( <. (/) , A >. = <. (/) , B >. <-> ( (/) = (/) /\\ A = B ) ) )' % ph)
    eqz = w.s([], 'eqid', '(/) = (/)')
    eqza = w.s([eqz], 'a1i', '( %s -> (/) = (/) )' % ph)
    o2 = w.s([eqza], 'biantrurd', '( %s -> ( A = B <-> ( (/) = (/) /\\ A = B ) ) )' % ph)
    o3 = w.s([o1, o2], 'bitr4d', '( %s -> ( <. (/) , A >. = <. (/) , B >. <-> A = B ) )' % ph)
    w.qed([e1, o3], 'bitrd', '( %s -> ( ( inl ` A ) = ( inl ` B ) <-> A = B ) )' % ph)
    return w.run()


if __name__ == '__main__':
    if want('tm2hrtyp'): tm2hrtyp()
    if want('tm2hrbr2'): tm2hrbr2()
    if want('tm2hmvv'): tm2hmvv()
    if want('tm2hstf'): tm2hstf()
    if want('tm2hsdm'): tm2hsdm()
    if want('tm2hid'): tm2hid()
    if want('tm2hssc'): tm2hssc()
    if want('tm2hssd'): tm2hssd()
    if want('tm2hle'): tm2hle()
    if want('tm2hun'): tm2hun()
    if want('tm2hseq'): tm2hseq()
    if want('tm2hsa1'): tm2hsa1()
    if want('tm2hcfgss'): tm2hcfgss()
    if want('tm2hstep'): tm2hstep()
    if want('inlinj'): inlinj()
    if want('tm2hcfgsr'): tm2hcfgsr()
