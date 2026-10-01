"""Sortie C8, section 2 small lemmas: slitq, crectpa, crectaff."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c8lib import *


def gen_slitq():
    w = W('slitq', 'A quotient ` U / V ` with ` abs ( U - V ) < M <_ abs V ` lies in the slit plane: its distance from ` 1 ` is below ` 1 ` .')
    A0 = '( ( U e. CC /\\ V e. CC ) /\\ ( M e. RR+ /\\ M <_ ( abs ` V ) /\\ ( abs ` ( U - V ) ) < M ) )'
    uv = w.s([], 'simpl', '( %s -> ( U e. CC /\\ V e. CC ) )' % A0)
    h3 = w.s([], 'simpr', '( %s -> ( M e. RR+ /\\ M <_ ( abs ` V ) /\\ ( abs ` ( U - V ) ) < M ) )' % A0)
    uc = w.s([uv, w.inst('simpl')], 'syl', '( %s -> U e. CC )' % A0)
    vc = w.s([uv, w.inst('simpr')], 'syl', '( %s -> V e. CC )' % A0)
    mrp = w.s([h3, w.inst('simp1')], 'syl', '( %s -> M e. RR+ )' % A0)
    mle = w.s([h3, w.inst('simp2')], 'syl', '( %s -> M <_ ( abs ` V ) )' % A0)
    dlt = w.s([h3, w.inst('simp3')], 'syl', '( %s -> ( abs ` ( U - V ) ) < M )' % A0)
    mr = w.s([mrp], 'rpred', '( %s -> M e. RR )' % A0)
    mpos = w.s([mrp], 'rpgt0d', '( %s -> 0 < M )' % A0)
    avr = w.s([vc], 'abscld', '( %s -> ( abs ` V ) e. RR )' % A0)
    z0 = w.s([], '0red', '( %s -> 0 e. RR )' % A0)
    avp = w.s([z0, mr, avr, mpos, mle], 'ltletrd', '( %s -> 0 < ( abs ` V ) )' % A0)
    vne = w.s([avp, w.s([vc, w.inst('absgt0')], 'syl', '( %s -> ( V =/= 0 <-> 0 < ( abs ` V ) ) )' % A0)], 'mpbird', '( %s -> V =/= 0 )' % A0)
    W_ = '( U / V )'
    wc = w.s([uc, vc, vne], 'divcld', '( %s -> %s e. CC )' % (A0, W_))
    one = w.s([], '1cnd', '( %s -> 1 e. CC )' % A0)
    # ( U - V ) / V = W - 1
    e1 = w.s([uc, vc, vc, vne], 'divsubdird', '( %s -> ( ( U - V ) / V ) = ( %s - ( V / V ) ) )' % (A0, W_))
    e2 = w.s([vc, vne], 'dividd', '( %s -> ( V / V ) = 1 )' % A0)
    e3 = w.s([e1, w.s([e2], 'oveq2d', '( %s -> ( %s - ( V / V ) ) = ( %s - 1 ) )' % (A0, W_, W_))], 'eqtrd',
             '( %s -> ( ( U - V ) / V ) = ( %s - 1 ) )' % (A0, W_))
    uvc = w.s([uc, vc], 'subcld', '( %s -> ( U - V ) e. CC )' % A0)
    a1 = w.s([uvc, vc, vne], 'absdivd', '( %s -> ( abs ` ( ( U - V ) / V ) ) = ( ( abs ` ( U - V ) ) / ( abs ` V ) ) )' % A0)
    a2 = w.s([w.s([e3], 'fveq2d', '( %s -> ( abs ` ( ( U - V ) / V ) ) = ( abs ` ( %s - 1 ) ) )' % (A0, W_)), a1], 'eqtr3d',
             '( %s -> ( abs ` ( %s - 1 ) ) = ( ( abs ` ( U - V ) ) / ( abs ` V ) ) )' % (A0, W_))
    avrp = w.s([avr, avp], 'elrpd', '( %s -> ( abs ` V ) e. RR+ )' % A0)
    auv = w.s([uvc], 'abscld', '( %s -> ( abs ` ( U - V ) ) e. RR )' % A0)
    lt1 = w.s([auv, mr, avr, dlt, mle], 'ltletrd', '( %s -> ( abs ` ( U - V ) ) < ( abs ` V ) )' % A0)
    mul1 = w.s([w.s([avr], 'recnd', '( %s -> ( abs ` V ) e. CC )' % A0)], 'mulridd', '( %s -> ( ( abs ` V ) x. 1 ) = ( abs ` V ) )' % A0)
    lt3 = w.s([lt1, w.s([mul1], 'eqcomd', '( %s -> ( abs ` V ) = ( ( abs ` V ) x. 1 ) )' % A0)], 'breqtrd',
              '( %s -> ( abs ` ( U - V ) ) < ( ( abs ` V ) x. 1 ) )' % A0)
    lt4 = w.s([lt3, w.s([auv, w.s([], '1red', '( %s -> 1 e. RR )' % A0), avrp], 'ltdivmuld',
                        '( %s -> ( ( ( abs ` ( U - V ) ) / ( abs ` V ) ) < 1 <-> ( abs ` ( U - V ) ) < ( ( abs ` V ) x. 1 ) ) )' % A0)], 'mpbird',
              '( %s -> ( ( abs ` ( U - V ) ) / ( abs ` V ) ) < 1 )' % A0)
    lt5 = w.s([a2, lt4], 'eqbrtrd', '( %s -> ( abs ` ( %s - 1 ) ) < 1 )' % (A0, W_))
    # 1 - Re W <_ abs ( 1 - W ) = abs ( W - 1 )
    omw = w.s([one, wc], 'subcld', '( %s -> ( 1 - %s ) e. CC )' % (A0, W_))
    r1 = w.s([omw, w.inst('releabs')], 'syl', '( %s -> ( Re ` ( 1 - %s ) ) <_ ( abs ` ( 1 - %s ) ) )' % (A0, W_, W_))
    r2 = w.s([one, wc, w.inst('resub')], 'syl2anc', '( %s -> ( Re ` ( 1 - %s ) ) = ( ( Re ` 1 ) - ( Re ` %s ) ) )' % (A0, W_, W_))
    r3 = w.s([w.s([w.s([], 're1', '( Re ` 1 ) = 1')], 'a1i', '( %s -> ( Re ` 1 ) = 1 )' % A0)], 'oveq1d',
             '( %s -> ( ( Re ` 1 ) - ( Re ` %s ) ) = ( 1 - ( Re ` %s ) ) )' % (A0, W_, W_))
    r4 = w.s([r2, r3], 'eqtrd', '( %s -> ( Re ` ( 1 - %s ) ) = ( 1 - ( Re ` %s ) ) )' % (A0, W_, W_))
    r5 = w.s([one, wc], 'abssubd', '( %s -> ( abs ` ( 1 - %s ) ) = ( abs ` ( %s - 1 ) ) )' % (A0, W_, W_))
    r6 = w.s([w.s([r4, r1], 'eqbrtrrd', '( %s -> ( 1 - ( Re ` %s ) ) <_ ( abs ` ( 1 - %s ) ) )' % (A0, W_, W_)), r5], 'breqtrd',
             '( %s -> ( 1 - ( Re ` %s ) ) <_ ( abs ` ( %s - 1 ) ) )' % (A0, W_, W_))
    wr = w.s([wc], 'recld', '( %s -> ( Re ` %s ) e. RR )' % (A0, W_))
    one_r = w.s([], '1red', '( %s -> 1 e. RR )' % A0)
    omr = w.s([one_r, wr], 'resubcld', '( %s -> ( 1 - ( Re ` %s ) ) e. RR )' % (A0, W_))
    awr = w.s([w.s([wc, one], 'subcld', '( %s -> ( %s - 1 ) e. CC )' % (A0, W_))], 'abscld', '( %s -> ( abs ` ( %s - 1 ) ) e. RR )' % (A0, W_))
    r7 = w.s([omr, awr, one_r, r6, lt5], 'lelttrd', '( %s -> ( 1 - ( Re ` %s ) ) < 1 )' % (A0, W_))
    r8 = w.s([r7, w.s([wr, one_r, w.inst('ltsubpos')], 'syl2anc', '( %s -> ( 0 < ( Re ` %s ) <-> ( 1 - ( Re ` %s ) ) < 1 ) )' % (A0, W_, W_))],
             'mpbird', '( %s -> 0 < ( Re ` %s ) )' % (A0, W_))
    w.qed([wc, r8, w.inst('elslitre')], 'syl2anc', '( %s -> %s e. %s )' % (A0, W_, SLIT))
    return run8(w)


def gen_crectpa():
    w = W('crectpa', 'A point of a rectangle is within the half-perimeter of the lower left corner.')
    A0 = '( ( A e. CC /\\ B e. CC ) /\\ Z e. ( A crect B ) )'
    ab = w.s([], 'simpl', '( %s -> %s )' % (A0, AB))
    zin = w.s([], 'simpr', '( %s -> Z e. ( A crect B ) )' % A0)
    e = rectel(w, A0, zin, ab, 'Z')
    zc, ac = e['xc'], e['ac']
    zac = w.s([zc, ac], 'subcld', '( %s -> ( Z - A ) e. CC )' % A0)
    c1 = w.s([zac, w.inst('abscrle')], 'syl', '( %s -> ( abs ` ( Z - A ) ) <_ ( ( abs ` ( Re ` ( Z - A ) ) ) + ( abs ` ( Im ` ( Z - A ) ) ) ) )' % A0)
    re1 = w.s([zc, ac, w.inst('resub')], 'syl2anc', '( %s -> ( Re ` ( Z - A ) ) = ( ( Re ` Z ) - ( Re ` A ) ) )' % A0)
    im1 = w.s([zc, ac, w.inst('imsub')], 'syl2anc', '( %s -> ( Im ` ( Z - A ) ) = ( ( Im ` Z ) - ( Im ` A ) ) )' % A0)
    dr = w.s([e['xr'], e['ar']], 'resubcld', '( %s -> ( ( Re ` Z ) - ( Re ` A ) ) e. RR )' % A0)
    di = w.s([e['xi'], e['ai']], 'resubcld', '( %s -> ( ( Im ` Z ) - ( Im ` A ) ) e. RR )' % A0)
    dr0 = w.s([e['lar'], w.s([e['xr'], e['ar']], 'subge0d', '( %s -> ( 0 <_ ( ( Re ` Z ) - ( Re ` A ) ) <-> ( Re ` A ) <_ ( Re ` Z ) ) )' % A0)],
              'mpbird', '( %s -> 0 <_ ( ( Re ` Z ) - ( Re ` A ) ) )' % A0)
    di0 = w.s([e['lai'], w.s([e['xi'], e['ai']], 'subge0d', '( %s -> ( 0 <_ ( ( Im ` Z ) - ( Im ` A ) ) <-> ( Im ` A ) <_ ( Im ` Z ) ) )' % A0)],
              'mpbird', '( %s -> 0 <_ ( ( Im ` Z ) - ( Im ` A ) ) )' % A0)
    ar1 = w.s([w.s([re1], 'fveq2d', '( %s -> ( abs ` ( Re ` ( Z - A ) ) ) = ( abs ` ( ( Re ` Z ) - ( Re ` A ) ) ) )' % A0),
               w.s([dr, dr0], 'absidd', '( %s -> ( abs ` ( ( Re ` Z ) - ( Re ` A ) ) ) = ( ( Re ` Z ) - ( Re ` A ) ) )' % A0)], 'eqtrd',
              '( %s -> ( abs ` ( Re ` ( Z - A ) ) ) = ( ( Re ` Z ) - ( Re ` A ) ) )' % A0)
    ai1 = w.s([w.s([im1], 'fveq2d', '( %s -> ( abs ` ( Im ` ( Z - A ) ) ) = ( abs ` ( ( Im ` Z ) - ( Im ` A ) ) ) )' % A0),
               w.s([di, di0], 'absidd', '( %s -> ( abs ` ( ( Im ` Z ) - ( Im ` A ) ) ) = ( ( Im ` Z ) - ( Im ` A ) ) )' % A0)], 'eqtrd',
              '( %s -> ( abs ` ( Im ` ( Z - A ) ) ) = ( ( Im ` Z ) - ( Im ` A ) ) )' % A0)
    s1 = w.s([ar1, ai1], 'oveq12d', '( %s -> ( ( abs ` ( Re ` ( Z - A ) ) ) + ( abs ` ( Im ` ( Z - A ) ) ) ) = ( ( ( Re ` Z ) - ( Re ` A ) ) + ( ( Im ` Z ) - ( Im ` A ) ) ) )' % A0)
    c2 = w.s([c1, s1], 'breqtrd', '( %s -> ( abs ` ( Z - A ) ) <_ ( ( ( Re ` Z ) - ( Re ` A ) ) + ( ( Im ` Z ) - ( Im ` A ) ) ) )' % A0)
    l1 = w.s([e['xr'], e['br'], e['ar'], e['lbr']], 'lesub1dd', '( %s -> ( ( Re ` Z ) - ( Re ` A ) ) <_ ( ( Re ` B ) - ( Re ` A ) ) )' % A0)
    l2 = w.s([e['xi'], e['bi'], e['ai'], e['lbi']], 'lesub1dd', '( %s -> ( ( Im ` Z ) - ( Im ` A ) ) <_ ( ( Im ` B ) - ( Im ` A ) ) )' % A0)
    br_ = w.s([e['br'], e['ar']], 'resubcld', '( %s -> ( ( Re ` B ) - ( Re ` A ) ) e. RR )' % A0)
    bi_ = w.s([e['bi'], e['ai']], 'resubcld', '( %s -> ( ( Im ` B ) - ( Im ` A ) ) e. RR )' % A0)
    l3 = w.s([dr, di, br_, bi_, l1, l2], 'le2addd', '( %s -> ( ( ( Re ` Z ) - ( Re ` A ) ) + ( ( Im ` Z ) - ( Im ` A ) ) ) <_ %s )' % (A0, PER))
    azr = w.s([zac], 'abscld', '( %s -> ( abs ` ( Z - A ) ) e. RR )' % A0)
    w.qed([azr, w.s([dr, di], 'readdcld', '( %s -> ( ( ( Re ` Z ) - ( Re ` A ) ) + ( ( Im ` Z ) - ( Im ` A ) ) ) e. RR )' % A0),
           w.s([br_, bi_], 'readdcld', '( %s -> %s e. RR )' % (A0, PER)), c2, l3], 'letrd', '( %s -> ( abs ` ( Z - A ) ) <_ %s )' % (A0, PER))
    return run8(w)


def gen_crectaff():
    w = W('crectaff', 'The point ` A + T ( Z - A ) ` , ` 0 <_ T <_ 1 ` , of the segment from the lower left corner to a point of the rectangle lies in the rectangle.')
    A0 = '( ( ( A e. CC /\\ B e. CC ) /\\ %s ) /\\ ( Z e. ( A crect B ) /\\ T e. ( 0 [,] 1 ) ) )' % GEO
    abg = w.s([], 'simpl', '( %s -> ( %s /\\ %s ) )' % (A0, AB, GEO))
    ab = w.s([abg, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, AB))
    zt = w.s([], 'simpr', '( %s -> ( Z e. ( A crect B ) /\\ T e. ( 0 [,] 1 ) ) )' % A0)
    zin = w.s([zt, w.inst('simpl')], 'syl', '( %s -> Z e. ( A crect B ) )' % A0)
    tin = w.s([zt, w.inst('simpr')], 'syl', '( %s -> T e. ( 0 [,] 1 ) )' % A0)
    ain = w.s([abg, w.inst('crectcnr1')], 'syl', '( %s -> A e. ( A crect B ) )' % A0)
    ac = w.s([ab, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % A0)
    crss = w.s([ab, w.inst('crectss')], 'syl', '( %s -> ( A crect B ) C_ CC )' % A0)
    zc = w.s([crss, zin], 'sseldd', '( %s -> Z e. CC )' % A0)
    cvx = w.s([ab, w.s([ain, zin], 'jca', '( %s -> ( A e. ( A crect B ) /\\ Z e. ( A crect B ) ) )' % A0), w.inst('crectcvx')], 'syl2anc',
              '( %s -> ( A cseg Z ) C_ ( A crect B ) )' % A0)
    P = AFF('T', 'Z')
    # P e. ( A cseg Z ) via csegel
    el = w.s([ac, zc, w.inst('csegel')], 'syl2anc', '( %s -> ( %s e. ( A cseg Z ) <-> E. t e. ( 0 [,] 1 ) %s = %s ) )' % (A0, P, P, AFF('t', 'Z')))
    sub = w.s([], 'oveq1', '( t = T -> ( t x. ( Z - A ) ) = ( T x. ( Z - A ) ) )')
    sub2 = w.s([sub], 'oveq2d', '( t = T -> %s = %s )' % (AFF('t', 'Z'), P))
    sub3 = w.s([sub2], 'eqeq2d', '( t = T -> ( %s = %s <-> %s = %s ) )' % (P, AFF('t', 'Z'), P, P))
    eq = w.s([], 'eqidd', '( %s -> %s = %s )' % (A0, P, P))
    rsp = w.s([sub3], 'rspcev', '( ( T e. ( 0 [,] 1 ) /\\ %s = %s ) -> E. t e. ( 0 [,] 1 ) %s = %s )' % (P, P, P, AFF('t', 'Z')))
    ex = w.s([tin, eq, rsp], 'syl2anc', '( %s -> E. t e. ( 0 [,] 1 ) %s = %s )' % (A0, P, AFF('t', 'Z')))
    pin = w.s([ex, el], 'mpbird', '( %s -> %s e. ( A cseg Z ) )' % (A0, P))
    w.qed([cvx, pin], 'sseldd', '( %s -> %s e. ( A crect B ) )' % (A0, P))
    return run8(w)


if __name__ == '__main__':
    for g in [gen_slitq, gen_crectpa, gen_crectaff]:
        g()
