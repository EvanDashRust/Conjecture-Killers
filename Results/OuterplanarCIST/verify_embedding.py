"""Verify the triangulated-sphere certificate for the base graph."""

import ast
from collections import defaultdict
from itertools import combinations
from pathlib import Path
import re


def lean_list(name):
    source = Path(__file__).with_name("Proof.lean").read_text()
    match = re.search(rf"^def {name} : .*? :=\s*(\[[^\]]*\])", source, re.M | re.S)
    if match is None:
        raise ValueError(f"Could not read {name}")
    return ast.literal_eval(match[1])


def undirected(x, y):
    return (min(x, y), max(x, y))


def arcs(face):
    x, y, z = face
    return ((x, y), (y, z), (z, x))


def reachable(start, neighbors):
    seen = {start}
    todo = [start]
    while todo:
        for nxt in neighbors[todo.pop()]:
            if nxt not in seen:
                seen.add(nxt)
                todo.append(nxt)
    return seen


def verify():
    triangles = lean_list("triangleList")
    masks = lean_list("neighborMasks")
    flipped = {0, 2, 3, 5, 6, 7, 8, 9, 11, 14, 15, 16, 17, 19, 21,
               22, 23, 24, 26, 27, 29, 35, 40}
    assert len(triangles) == 46
    assert len(masks) == 25
    assert triangles[0] == (0, 1, 2)

    # The 25 core vertices are followed by one stellar vertex per core face.
    faces = []
    core_edges = set()
    for f, (a, b, c) in enumerate(triangles):
        assert 0 <= a < b < c < 25
        core_edges.update(undirected(u, v) for u, v in arcs((a, b, c)))
        if f in flipped:
            b, c = c, b
        p = 25 + f
        faces.extend(((a, b, p), (b, c, p), (c, a, p)))
    for u, mask in enumerate(masks):
        assert mask == sum(1 << v for v in range(25)
                           if undirected(u, v) in core_edges)

    # Each directed edge occurs once, and it has the opposite orientation
    # on the other face. The links at vertices must each be a single cycle.
    directed = {}
    links = defaultdict(dict)
    neighbors = defaultdict(set)
    for f, (a, b, c) in enumerate(faces):
        for u, v, w in ((a, b, c), (b, c, a), (c, a, b)):
            assert (u, v) not in directed
            directed[u, v] = f
            links[u][v] = w
            neighbors[u].add(v)
    assert all((v, u) in directed for u, v in directed)
    assert set(neighbors) == set(range(71))
    assert len(reachable(0, neighbors)) == 71
    for u, link in links.items():
        start = min(link)
        v = start
        visited = set()
        while v not in visited:
            visited.add(v)
            v = link[v]
        assert v == start
        assert visited == set(link) == neighbors[u]
    edge_count = len(directed) // 2
    assert 71 - edge_count + len(faces) == 2
    for x, y in combinations(range(71), 2):
        remaining = set(range(71)) - {x, y}
        induced = {u: neighbors[u] & remaining for u in remaining}
        assert reachable(min(remaining), induced) == remaining

    # For a triangulation peeled from a face, the rounds are the graph
    # distance layers from its three boundary vertices.
    outer = {0, 1, 25}
    assert any(set(f) == outer for f in faces)
    layers = [outer]
    unseen = set(range(71)) - outer
    while unseen:
        new = set().union(*(neighbors[u] for u in layers[-1])) & unseen
        assert new
        layers.append(new)
        unseen -= new
    assert [len(layer) for layer in layers] == [3, 32, 33, 3]
    print(f"Embedding certificate: 71 vertices, {edge_count} edges, {len(faces)} faces")
    print("All 2485 two-vertex deletions leave the graph connected")
    print("Peeling rounds:", [len(layer) for layer in layers])


if __name__ == "__main__":
    verify()
