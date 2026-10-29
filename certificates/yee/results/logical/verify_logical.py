#!/usr/bin/env python3
"""Exact checks of the constructive R5 implementation on reproducible cases.

No floating point or third-party package is used. These are implementation
checks, not a substitute for the all-input proof in r5_constructive_proof.md.
The program fails on a missing invariant and never accepts saved PASS text.
"""
from __future__ import annotations

from collections import defaultdict
from fractions import Fraction as F
from itertools import permutations
from random import Random
import hashlib
import json
import sys
import time

if not __debug__:
    raise RuntimeError("Assertions are required; do not run this verifier with -O.")


def circuit(matrix, bits):
    """Build the fixed-alphabet square constraint matrix as sparse row dicts."""
    n = len(matrix)
    assert all(len(row) == n for row in matrix)
    gates = []

    def gate(terms):
        terms = [(i, F(w)) for i, w in terms if w]
        idx = n + len(gates)
        assert all(i < idx for i, _ in terms)
        assert len({i for i, _ in terms}) == len(terms)
        gates.append(terms)
        return idx

    def copies(root, count):
        assert count >= 1
        if count == 1:
            return [root]
        left = gate([(root, 1)])
        right = gate([(root, 1)])
        a = count // 2
        return copies(left, a) + copies(right, count - a)

    uses = [0] * n
    entries = []
    for i, row in enumerate(matrix):
        for j, w in enumerate(row):
            w = F(w)
            if not w:
                continue
            assert 0 < abs(w) < 1
            numerator = abs(w) * (1 << bits)
            assert numerator.denominator == 1
            digits = [(int(numerator) >> (bits - k)) & 1
                      for k in range(1, bits + 1)]
            uses[j] += sum(digits)
            entries.append((i, j, 1 if w > 0 else -1, digits))
    assert all(uses)
    leaves = [iter(copies(j, uses[j])) for j in range(n)]
    terms_by_row = [[] for _ in range(n)]
    for i, j, sign, digits in entries:
        prev = None
        for bit in reversed(digits):
            terms = [] if prev is None else [(prev, F(1, 2))]
            if bit:
                terms.append((next(leaves[j]), F(1, 2)))
            prev = gate(terms)
        product = gate([(prev, sign)])
        terms_by_row[i].append(product)
    outputs = []
    for terms in terms_by_row:
        assert terms
        while len(terms) > 1:
            terms = [gate([(terms[j], 1), (terms[j + 1], 1)])
                     if j + 1 < len(terms) else terms[j]
                     for j in range(0, len(terms), 2)]
        outputs.append(terms[0])
    rows = [{o: F(1)} for o in outputs]
    for k, terms in enumerate(gates):
        row = {n + k: F(1)}
        for i, w in terms:
            row[i] = -w
        rows.append(row)
    return gates, outputs, rows


def check_circuit(matrix, bits):
    n = len(matrix)
    gates, outputs, rows = circuit(matrix, bits)
    size = len(rows)
    assert size == n + len(gates)
    cols = [0] * size
    col_abs = [F(0)] * size
    alphabet = {F(1), F(-1), F(1, 2), F(-1, 2)}
    for row in rows:
        assert len(row) <= 3
        assert sum(abs(v) for v in row.values()) <= 3
        for j, value in row.items():
            assert value in alphabet
            cols[j] += 1
            col_abs[j] += abs(value)
    assert max(cols) <= 3 and max(col_abs) <= 3
    symbolic = [{j: F(1)} for j in range(n)]
    for terms in gates:
        out = defaultdict(F)
        for idx, weight in terms:
            for j, coefficient in symbolic[idx].items():
                out[j] += weight * coefficient
        symbolic.append(dict(out))
    for i, idx in enumerate(outputs):
        assert [symbolic[idx].get(j, F(0)) for j in range(n)] == list(matrix[i])
    # T inverse: enumerate signed path sums exactly, one gate-error source at a time.
    count = len(gates)
    for source in range(count):
        vals = [F(0)] * n
        for k, terms in enumerate(gates):
            val = sum(weight * vals[idx] for idx, weight in terms)
            if k == source:
                val += 1
            vals.append(val)
        assert max(abs(x) for x in vals) <= size
    return {"dimension": size, "gate_count": count,
            "nonzeros": sum(map(len, rows))}


def matching_colors(q, destinations):
    """q-regular bipartite multigraph edge coloring by Euler splitting."""
    assert q > 0 and q & (q - 1) == 0
    assert len(destinations) == q * q
    endpoints = [(token // q, q + destinations[token] // q)
                 for token in range(q * q)]
    colors = [-1] * (q * q)

    def split(edges, degree, offset):
        if degree == 1:
            for e in edges:
                colors[e] = offset
            return
        adj = [[] for _ in range(2 * q)]
        for e in edges:
            u, v = endpoints[e]
            adj[u].append(e)
            adj[v].append(e)
        assert all(len(v) == degree for v in adj)
        used = set()
        halves = [[], []]
        for start in range(2 * q):
            while adj[start] and adj[start][-1] in used:
                adj[start].pop()
            if not adj[start]:
                continue
            vertex_stack = [start]
            edge_stack = []
            circuit_edges = []
            while vertex_stack:
                v = vertex_stack[-1]
                while adj[v] and adj[v][-1] in used:
                    adj[v].pop()
                if adj[v]:
                    e = adj[v].pop()
                    used.add(e)
                    a, b = endpoints[e]
                    vertex_stack.append(b if v == a else a)
                    edge_stack.append(e)
                else:
                    vertex_stack.pop()
                    if edge_stack:
                        circuit_edges.append(edge_stack.pop())
            assert len(circuit_edges) % 2 == 0
            for k, e in enumerate(circuit_edges):
                halves[k % 2].append(e)
        assert len(used) == len(edges)
        split(halves[0], degree // 2, offset)
        split(halves[1], degree // 2, offset + degree // 2)

    split(list(range(q * q)), q, 0)
    for row in range(q):
        assert sorted(colors[row * q:(row + 1) * q]) == list(range(q))
    for color in range(q):
        assert sorted(destinations[e] // q for e, c in enumerate(colors)
                      if c == color) == list(range(q))
    return colors


def expand(points):
    out = [points[0]]
    for target in points[1:]:
        origin = out[-1]
        axes = [k for k in range(3) if origin[k] != target[k]]
        assert len(axes) == 1
        axis = axes[0]
        step = 1 if target[axis] > origin[axis] else -1
        while out[-1] != target:
            p = list(out[-1])
            p[axis] += step
            out.append(tuple(p))
    return out


SWAP_A = [(0, 0, 0), (0, 0, 4), (0, 4, 4), (16, 4, 4),
          (16, 4, 12), (16, 0, 12), (16, 0, 16)]
SWAP_B = [(16, 0, 0), (16, 0, 8), (16, -4, 8), (0, -4, 8),
          (0, -4, 12), (0, 0, 12), (0, 0, 16)]


def permutation_paths(q, destinations, tracked=None):
    assert sorted(destinations) == list(range(q * q))
    colors = matching_colors(q, destinations)
    slots = list(range(q * q))
    tracked = set(range(q * q) if tracked is None else tracked)
    paths = {t: [(16 * (t % q), 16 * (t // q), 0)] for t in tracked}
    z = 0
    for stage in range(3):
        axis = 0 if stage != 1 else 1
        def key(token):
            if stage == 0:
                return colors[token]
            if stage == 1:
                return destinations[token] // q
            return destinations[token] % q
        for time in range(2 * q):
            swaps = []
            paired = set()
            for line in range(q):
                for p in range(time % 2, q - 1, 2):
                    s0 = line * q + p if axis == 0 else p * q + line
                    s1 = s0 + (1 if axis == 0 else q)
                    if key(slots[s0]) > key(slots[s1]):
                        swaps.append((s0, s1))
                        paired.update((s0, s1))
            for s0, s1 in swaps:
                x0, y0 = 16 * (s0 % q), 16 * (s0 // q)
                for slot, template in ((s0, SWAP_A), (s1, SWAP_B)):
                    token = slots[slot]
                    if token in tracked:
                        pts = [(x0 + (y if axis else x),
                                y0 + (x if axis else y), z + h)
                               for x, y, h in template]
                        path = expand(pts)
                        assert paths[token][-1] == path[0]
                        paths[token].extend(path[1:])
                slots[s0], slots[s1] = slots[s1], slots[s0]
            for slot, token in enumerate(slots):
                if slot not in paired and token in tracked:
                    x, y = 16 * (slot % q), 16 * (slot // q)
                    path = expand([(x, y, z), (x, y, z + 16)])
                    assert paths[token][-1] == path[0]
                    paths[token].extend(path[1:])
            z += 16
    assert all(destinations[token] == slot for slot, token in enumerate(slots))
    for token, path in paths.items():
        dest = destinations[token]
        assert path[-1] == (16 * (dest % q), 16 * (dest // q), z)
    return paths, z


def check_disjoint(paths):
    occupied = {}
    for token, path in paths.items():
        assert len(set(path)) == len(path)
        for p, r in zip(path, path[1:]):
            assert sum(abs(a - b) for a, b in zip(p, r)) == 1
        for p in path:
            assert p not in occupied, (p, token, occupied.get(p))
            occupied[p] = token
    return len(occupied)


def graph_paths(bipartition, edges):
    """Route a simple bipartite degree-three graph and make lengths 1 mod 4."""
    U = len(bipartition)
    a = 1
    while a * a < U:
        a *= 2
    q = 2 * a
    incidents = [[] for _ in range(U)]
    for e, (v, w) in enumerate(edges):
        assert v != w and bipartition[v] != bipartition[w]
        incidents[v].append(e)
        incidents[w].append(e)
    assert all(len(x) <= 3 for x in incidents)
    ports = {}
    stars = {}
    offsets = [(0, 0), (1, 0), (0, 1)]
    vertices = {}
    for v, inc in enumerate(incidents):
        i, j = v % a, v // a
        x, y = 32 * i, 32 * j
        z = -16 + bipartition[v]
        vertices[v] = (x, y, z)
        for arm, e in enumerate(inc):
            dx, dy = offsets[arm]
            token = (2 * j + dy) * q + 2 * i + dx
            ports[(v, e)] = token
            points = [(x, y, z)]
            if dx or dy:
                points.append((x + 16 * dx, y + 16 * dy, z))
            points.append((x + 16 * dx, y + 16 * dy, 0))
            stars[(v, e)] = expand(points)
    destinations = [-1] * (q * q)
    for e, (v, w) in enumerate(edges):
        destinations[ports[(v, e)]] = 2 * e
        destinations[ports[(w, e)]] = 2 * e + 1
    unused = iter(range(2 * len(edges), q * q))
    for token in range(q * q):
        if destinations[token] == -1:
            destinations[token] = next(unused)
    legs, top = permutation_paths(q, destinations, ports.values())
    paths = {}
    for e, (v, w) in enumerate(edges):
        tv, tw = ports[(v, e)], ports[(w, e)]
        p, r = legs[tv], legs[tw]
        px, py, _ = p[-1]
        rx, ry, _ = r[-1]
        connector = expand([(px, py, top), (px, py, top + 16),
                            (rx, ry, top + 16), (rx, ry, top)])
        path = stars[(v, e)] + p[1:] + connector[1:]
        path += list(reversed(r))[1:]
        path += list(reversed(stars[(w, e)]))[1:]
        assert (len(path) - 1) % 2 == 1
        if (len(path) - 1) % 4 == 3:
            token = tv
            x, y = 16 * (token % q), 16 * (token // q)
            first = (x, y, -8)
            j = path.index(first)
            assert path[j + 1] == (x, y, -7)
            path[j + 1:j + 1] = [(x + 1, y, -8), (x + 1, y, -7)]
        assert (len(path) - 1) % 4 == 1
        assert len(path) - 1 <= 1024 * q
        paths[e] = path
    return vertices, paths, q


def check_graph(bipartition, edges):
    vertices, paths, q = graph_paths(bipartition, edges)
    used = {}
    for e, path in paths.items():
        v, w = edges[e]
        assert path[0] == vertices[v] and path[-1] == vertices[w]
        assert len(path) == len(set(path))
        for p, r in zip(path, path[1:]):
            assert sum(abs(a - b) for a, b in zip(p, r)) == 1
        for k, p in enumerate(path):
            if p in used:
                assert k in (0, len(path) - 1)
                old_e = used[p]
                assert p in (paths[old_e][0], paths[old_e][-1])
            used[p] = e
    return {"U": len(bipartition), "E": len(edges), "q": q,
            "unit_grid_vertices": len(used),
            "maximum_edge_length": max((len(p) - 1 for p in paths.values()), default=0)}


def check_path_inverse(n):
    assert n % 4 == 0 and n > 0
    # Solve each basis RHS using exact sparse recurrence, then check T X=I.
    inv = [[0] * n for _ in range(n)]
    for source in range(n):
        rhs = [int(j == source) for j in range(n)]
        x = [0] * (n + 2)
        for j in range(1, n, 2):
            x[j + 1] = rhs[j - 1] - x[j - 1]
        for j in range(n, 1, -2):
            x[j - 1] = rhs[j - 1] - x[j + 1]
        out = x[1:n + 1]
        for j in range(n):
            assert (out[j - 1] if j else 0) + (out[j + 1] if j + 1 < n else 0) == rhs[j]
            inv[j][source] = out[j]
    assert inv[0][0] == inv[-1][-1] == 0
    assert inv[0][-1] == inv[-1][0] == -1
    assert max(sum(map(abs, row)) for row in inv) <= n


def main():
    start_time = time.monotonic()
    rng = Random(20261027)
    cases = [([[F(1, 2), F(1, 4)], [F(-1, 4), F(1, 2)]], 2),
             ([[F(3, 8), F(-5, 16), F(0)],
               [F(0), F(7, 16), F(1, 8)],
               [F(1, 16), F(0), F(-1, 2)]], 4)]
    circuit_results = [check_circuit(*case) for case in cases]
    assert set(expand(SWAP_A)).isdisjoint(expand(SWAP_B))
    permutation_cases = 0
    permutation_vertices = 0
    for dest in permutations(range(4)):
        paths, _ = permutation_paths(2, list(dest))
        permutation_vertices += check_disjoint(paths)
        permutation_cases += 1
    for q, count in [(4, 12), (8, 6)]:
        for _ in range(count):
            dest = list(range(q * q))
            rng.shuffle(dest)
            paths, _ = permutation_paths(q, dest)
            permutation_vertices += check_disjoint(paths)
            permutation_cases += 1
    graph_results = []
    for half in range(1, 9):
        for _ in range(3):
            possible = [(v, half + w) for v in range(half) for w in range(half)]
            rng.shuffle(possible)
            degrees = [0] * (2 * half)
            edges = []
            for v, w in possible:
                if degrees[v] < 3 and degrees[w] < 3 and rng.randrange(3) != 0:
                    edges.append((v, w))
                    degrees[v] += 1
                    degrees[w] += 1
            graph_results.append(check_graph([0] * half + [1] * half, edges))
    for n in range(4, 65, 4):
        check_path_inverse(n)
    report = {
        "status": "PASS: finite exact implementation checks only",
        "python": sys.version,
        "seed": 20261027,
        "circuit_checks": circuit_results,
        "permutation_cases": permutation_cases,
        "permutation_vertices_checked": permutation_vertices,
        "graph_cases": graph_results,
        "path_inverse_internal_sizes": list(range(4, 65, 4)),
        "elapsed_seconds": time.monotonic() - start_time,
        "source_sha256": hashlib.sha256(open(__file__, "rb").read()).hexdigest(),
    }
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
