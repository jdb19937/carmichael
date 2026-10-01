"""T15 (c): content-node and family definitions (appended to sorties/t15.mm by hand-run)."""
import os, sys, re
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from t15lib import *

P = {k_: v_ for k_, v_ in load_preds().items() if k_ != 'TMIroot'}


def dline(text, extra=()):
    toks = text.split()
    sv = sorted(set(t for t in toks if re.match(r'^[a-z]$', t)) | set(extra))
    cv = []
    for t in toks:
        if re.match(r"^[A-Z](\d|'|\"|_)?$|^[A-Z]\d$", t) and t not in cv:
            cv.append(t)
    if not sv:
        return ''
    head = ('$d ' + ' '.join(sv) + ' $.') if len(sv) > 1 else ''
    return head + ''.join('  $d %s %s $.' % (' '.join(sv), c) for c in cv)


def fold(s, ind='      '):
    out, line = [], ''
    for t in s.split():
        if len(line) + len(t) + 1 > 76 - len(ind):
            out.append(line); line = t
        else:
            line = (line + ' ' + t).strip()
    out.append(line)
    return ('\n' + ind).join(out)


def main():
    kinds = [n for n in P if n != 'TMIpnv']
    toks = [ntok(n) for n in P] + ['TMpnF'] + [ftok(n) for n in CUSTOM]
    out = ['', '  $c ' + fold(' '.join(toks), '     ') + ' $.', '']
    # syntax
    for n in P:
        vs = [v for v in P[n][0] if v != 'M']
        out.append('  $( Extend class notation with the content node of %s. $)' % n)
        out.append('  c%s $a class ( %s %s ) $.' % (ntok(n).lower(), ntok(n), ' '.join(vs)))
    out.append('  $( Extend class notation with the pushNum label family. $)')
    out.append('  ctmpnf $a class ( TMpnF W N X ) $.')
    for n in CUSTOM:
        out.append('  $( Extend class notation with the label family of %s. $)' % n)
        out.append('  c%s $a class %s $.' % (ftok(n).lower(), fam_syn(n)))
    out.append('')
    # definitions
    for n in P:
        if n == 'TMIpnv':
            body = PNV_BODY
        else:
            body, _ = content_body(n, P)
        lhs = csyn(n, P)
        text = '%s = %s' % (lhs, body)
        out.append('  ${')
        out.append('    ' + dline(text))
        out.append('    $( The program content of the fragment installed by ~ df-%s : own labels carry its statements, family indices the content of the sub-fragments. $)' % P[n][2][3:])
        out.append('    df-%s $a |- %s $.' % (ntok(n).lower(), fold(text)))
        out.append('  $}')
    text = '( TMpnF W N X ) = %s' % PNF_BODY
    out.append('  ${\n    %s\n    $( The label family of a pushNum fragment ( ~ df-tmipnv ): the labels of the addresses ` ( W ++ <" k "> ) ` and the exit ` X ` at the last index. $)\n    df-tmpnf $a |- %s $.\n  $}' % (dline(text), fold(text)))
    for n in CUSTOM:
        text = '%s = %s' % (fam_syn(n), fam_body(n, P))
        out.append('  ${\n    %s\n    $( The label family of %s: pushNum and family-bearing children get their families, every other index its address label. $)\n    df-%s $a |- %s $.\n  $}' % (dline(text), n, ftok(n).lower(), fold(text)))
    return '\n'.join(out) + '\n'


if __name__ == '__main__':
    sys.stdout.write(main())
