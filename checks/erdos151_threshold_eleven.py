"""Exact finite checks for the clique-transversal threshold H(n) <= 11."""
from itertools import combinations


def has_independent_set(neighbors, available, target):
    if target == 0:
        return True
    while available.bit_count() >= target:
        vertex_bit = available & -available
        available ^= vertex_bit
        row = neighbors[vertex_bit.bit_length() - 1]
        if has_independent_set(neighbors, available & ~row, target - 1):
            return True
    return False


def check_ramsey_witness(graph, forbidden_size):
    size = len(graph)
    for v, row in enumerate(graph):
        assert not (row >> v & 1)
        for w in range(size):
            assert (row >> w & 1) == (graph[w] >> v & 1)
            if row >> w & 1:
                assert row & graph[w] == 0
    assert not has_independent_set(graph, (1 << size) - 1, forbidden_size)


def local_extension(outsider_count, marked_count):
    """Enumerate all labelled K4-free graphs without independent triples.

    Mark the first marked_count vertices. This covers arbitrary marked sets
    of that size by relabelling, and smaller sets by adding dummy marks.
    """
    adj = [0] * outsider_count
    triples = [
        tri for tri in combinations(range(outsider_count), 3)
        if sum(v < marked_count for v in tri) <= 1
    ]
    checked = 0

    def admits_triple():
        for tri in triples:
            edges = [(i, j) for i, j in combinations(tri, 2) if adj[i] >> j & 1]
            if len(edges) < 3 and all(adj[i] & adj[j] for i, j in edges):
                return True
        return False

    def enumerate_rows(v):
        nonlocal checked
        if v == outsider_count:
            checked += 1
            assert admits_triple(), (marked_count, adj)
            return
        for neighbors in range(1 << v):
            neighbor_list = [i for i in range(v) if neighbors >> i & 1]
            others = ((1 << v) - 1) ^ neighbors
            # The nonneighbors of the new vertex must form a clique to
            # avoid creating an independent triple.
            if any(adj[i] & others != others ^ (1 << i)
                   for i in range(v) if others >> i & 1):
                continue
            # The neighbors cannot contain a triangle, which would form a K4.
            if any((adj[i] >> j & 1) and (adj[i] & adj[j] & neighbors)
                   for i, j in combinations(neighbor_list, 2)):
                continue
            adj[v] = neighbors
            for i in neighbor_list:
                adj[i] |= 1 << v
            enumerate_rows(v + 1)
            for i in neighbor_list:
                adj[i] ^= 1 << v
            adj[v] = 0

    enumerate_rows(0)
    return checked


def main():
    # Cyclic distance graph for H(38)<=9.
    distances = {1, 3, 5, 12, 19}
    cyclic = [sum(1 << j for j in range(38)
                  if min((i-j) % 38, (j-i) % 38) in distances) for i in range(38)]
    check_ramsey_witness(cyclic, 10)
    # Geoffrey Exoo's 46-vertex witness, with bit j encoding neighbor j.
    # https://cs.indstate.edu/ge/RAMSEY/g.3.11.46
    graph46 = [int(s, 16) for s in WITNESS_46.split()]
    assert len(graph46) == 46
    check_ramsey_witness(graph46, 11)
    for a, m, expected in ((6, 0, 2812), (7, 2, 13842), (8, 4, 17640)):
        count = local_extension(a, m)
        assert count == expected
        print(f"{a} outsiders, {m} allowed marks: all {count:,} labelled graphs extend")
    print("Both Ramsey witnesses and the three local extension certificates passed.")


WITNESS_46 = """
22114000926
1102a0488011
1140c0202081
28411e03000
26144200882
205480212001
2001280a980
629401054
1c049041041
3241827000
f01ba0000
150880401051
200002188b88
90418026c
204504680200
42d04001042
1b03004a0020
80b4010600
1022b4000100
43040017402
1f0000403400
8002800443c
304011488a
28402c000648
3c0002000788
626d001040
100286e011
140892a00180
285008060049
40902a60082
200c02480314
a0108060826
10a001e411
48002050682
19004000c4a8
a406800ac00
38114480220
180024c8211
812804134
383200020108
203400110906
1880110059
229188800
8c91b10000
8409150806
18051805020
"""

if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run without -O to check all assertions.")
    main()
