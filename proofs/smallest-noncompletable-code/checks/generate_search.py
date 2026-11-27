#!/usr/bin/env python3
"""Generate the certificates of the finite search behind Lemma 7.

The search mirrors `SmallestNoncompletable.Search.dfs` in `lean/SmallestNoncompletable/SearchDefs.lean`
exactly: the same profiles, the same order of choices, the same pruning and the same quick tests at
the leaves. Each remaining leaf receives a certificate, in the order of the search:

* a prefix tree for Lemma 6, computed from the closure `H(W)` of the code or of its reversal, or
* two parsings of one word with different first words, which show that `W` is not a code.

Usage: python3 generate_search.py [OUTPUT_DIRECTORY]
The default output directory is `../lean/SmallestNoncompletable/Search`.
"""
import collections
import os
import sys
from itertools import accumulate

# (number of letter codewords, lengths of the long words)
PROFILES = [(2, (2, 4)), (2, (2, 5)), (2, (2, 6)), (2, (3, 4)), (2, (3, 5)), (2, (4, 4)),
            (3, (2, 4)), (3, (2, 5)), (3, (3, 4)), (4, (2, 4)),
            (1, (2, 2, 4)), (1, (2, 2, 5)), (1, (2, 3, 4)), (2, (2, 2, 4))]


def cut(lens, p):
    out = []
    for length in lens:
        out.append(p[:length])
        p = p[length:]
    return out


def rem_starts(lens, i):
    if not lens:
        return 0
    return (1 if i == 0 else 0) + rem_starts(lens[1:], max(i - lens[0], 0))


def rem_ends(lens, i):
    if not lens:
        return 0
    return (1 if i < lens[0] else 0) + rem_ends(lens[1:], max(i - lens[0], 0))


def is_start(lens, i):
    return bool(lens) and (i == 0 or (lens[0] <= i and is_start(lens[1:], i - lens[0])))


def is_end(lens, i):
    return bool(lens) and (i + 1 == lens[0] or (lens[0] <= i and is_end(lens[1:], i - lens[0])))


def done_count(lens, i):
    """Number of long words before position i when i follows a long word other than the last."""
    if len(lens) <= 1 or i == 0:
        return 0
    if i == lens[0]:
        return 1
    if lens[0] < i:
        n = done_count(lens[1:], i - lens[0])
        return 0 if n == 0 else n + 1
    return 0


def bit(m, x):
    return (m >> x) & 1


def missing(m, s, n):
    return sum(1 - bit(m, s + x) for x in range(n))


def is_product(dictionary, w):
    if not w:
        return True
    return any(d and w[:len(d)] == d and is_product(dictionary, w[len(d):]) for d in dictionary)


def tails(us, vs):
    return {v[len(u):] for u in us for v in vs if u != v and v[:len(u)] == u}


def hull(words):
    closure = set(words)
    while True:
        bigger = closure | tails(closure, closure)
        if bigger == closure:
            return closure
        closure = bigger


def read(nodes, w):
    node = ()
    for x in w:
        node = node + (x,) if node + (x,) in nodes else ()
    return node == ()


def tree_certificate(ws, k, rev):
    words = [tuple(reversed(w)) if rev else tuple(w) for w in ws]
    closure = hull(words)
    letters = {x for w in words for x in w}
    if all((x,) in closure for x in letters):
        return None
    minimal = [h for h in closure if not any(len(g) < len(h) and h[:len(g)] == g for g in closure)]
    nodes = {()} | {b[:i] for b in minimal for i in range(len(b))}
    assert all(read(nodes, w) for w in words)
    assert any((x,) in nodes for w in words for x in w)
    assert all(x < k for p in nodes for x in p)
    return sorted(nodes, key=lambda p: (len(p), p))


def ambiguity(ws):
    words = [tuple(w) for w in ws]
    queue = collections.deque()
    for a in range(len(words)):
        for b in range(len(words)):
            if a != b and words[b][:len(words[a])] == words[a]:
                queue.append(([a], [b], words[b][len(words[a]):]))
    while queue:
        behind, ahead, dangling = queue.popleft()
        if len(behind) + len(ahead) > 14:
            continue
        for c, w in enumerate(words):
            if w == dangling:
                return behind + [c], ahead
            if w[:len(dangling)] == dangling:
                queue.append((ahead, behind + [c], w[len(dangling):]))
            elif dangling[:len(w)] == w:
                queue.append((behind + [c], ahead, dangling[len(w):]))
    return None


def encode(digits):
    n = 0
    for i, d in enumerate(digits + [1]):
        assert 0 <= d < 16
        n += d * 16 ** i
    return n


def certificate(ws, k):
    for rev in (False, True):
        nodes = tree_certificate(ws, k, rev)
        if nodes is not None:
            digits = [1 if rev else 0]
            for p in nodes:
                digits.append(len(p))
                digits.extend(p)
            return encode(digits)
    found = ambiguity(ws)
    assert found is not None, ws
    first, second = found
    return encode([2, len(first)] + first + second)


def search(s, lens):
    m, t = sum(lens), len(lens)
    certs = []
    stats = collections.Counter()

    def prune(i, u, k, S, E):
        return (t <= k - s or rem_starts(lens, i) < missing(S, s, k - s)
                or rem_ends(lens, i) < missing(E, s, k - s) or (2 <= s and m - i < s - u))

    def word_ok(i, q):
        n = done_count(lens, i)
        if n == 0:
            return True
        length = lens[n - 1]
        w = q[i - length:i]
        earlier = [[x] for x in range(s)] + cut(lens[:n - 1], q[:i - length])
        return w not in earlier and not is_product(earlier, w)

    def leaf(k, q):
        longs = cut(lens, q)
        stats['leaves'] += 1
        duplicate = len(set(map(tuple, longs))) != len(longs)
        prefix_free = all(s <= w[0] for w in longs) and not any(
            len(v) < len(w) and w[:len(v)] == v for v in longs for w in longs)
        suffix_free = all(s <= w[-1] for w in longs) and not any(
            len(v) < len(w) and w[len(w) - len(v):] == v for v in longs for w in longs)
        if duplicate or prefix_free or suffix_free:
            return
        certs.append(certificate([[x] for x in range(s)] + longs, k))

    def dfs(i, u, k, S, E, q):
        stats['nodes'] += 1
        if prune(i, u, k, S, E) or not word_ok(i, q):
            return
        if i == m:
            leaf(k, q)
            return
        start, end = is_start(lens, i), is_end(lens, i)
        for j in list(range(min(u + 1, s))) + list(range(s, k + 1)):
            dfs(i + 1, max(u, j + 1) if j < s else u, max(k, j + 1) if s <= j else k,
                S | (1 << j) if start else S, E | (1 << j) if end else E, q + [j])

    dfs(0, 0, s, 0, 0, [])
    return certs, stats


HEADER = """module

public import SmallestNoncompletable.SearchDefs

/-! # Search certificates for the profile with {s} letter codewords and long words of lengths
{lens}

Generated by `checks/generate_search.py`. -/

@[expose] public section

namespace SmallestNoncompletable.Search

"""


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    out = sys.argv[1] if len(sys.argv) > 1 else os.path.join(
        here, '..', 'lean', 'SmallestNoncompletable', 'Search')
    os.makedirs(out, exist_ok=True)
    total = collections.Counter()
    for idx, (s, lens) in enumerate(PROFILES):
        certs, stats = search(s, list(lens))
        total.update(stats)
        total['certificates'] += len(certs)
        name = f'{idx:02d}'
        body = HEADER.format(s=s, lens=list(lens))
        body += f"/-- The profile `{s}`, `{list(lens)}`. -/\n"
        body += f"def prof{name} : Prof := ⟨{s}, {list(lens)}⟩\n\n"
        body += f"/-- The certificates, in the order of the search. -/\ndef certs{name} : List ℕ := [\n"
        rows = ['  ' + ', '.join(map(str, certs[a:a + 6])) for a in range(0, len(certs), 6)]
        body += ',\n'.join(rows) + ']\n\n'
        body += f"theorem run{name} : run prof{name} certs{name} = true := by decide +kernel\n\n"
        body += "end SmallestNoncompletable.Search\n"
        with open(os.path.join(out, f'P{name}.lean'), 'w') as f:
            f.write(body)
        print(f'profile {s} {list(lens)}: {stats["nodes"]} nodes, {stats["leaves"]} leaves, '
              f'{len(certs)} certificates')
    print(f'total: {total["nodes"]} nodes, {total["leaves"]} leaves, '
          f'{total["certificates"]} certificates')


if __name__ == '__main__':
    main()
