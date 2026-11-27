"""Verify that no group-developed pair of order 12 extends to an affine plane.

Pure Python 3.10+. Run with assertions enabled. Pass --all-maps to repeat
the coverage classification on all normalized maps without orbit reduction.
"""
from collections import Counter
from itertools import combinations, permutations, product
import sys


N = 12
PAIRS = tuple(combinations(range(N), 2))
# normalized maps, orbit representatives, representatives passing pair coverage,
# total normalized maps passing pair coverage
EXPECTED = {
    "C12": (0, 0, 0, 0),
    "C3 x C2 x C2": (16512, 149, 1, 12),
    "D12": (6336, 72, 0, 0),
    "Dic3": (0, 0, 0, 0),
    "A4": (3840, 21, 0, 0),
}


def group_tables():
    even = [p for p in permutations(range(4))
            if sum(p[i] > p[j] for i, j in combinations(range(4), 2)) % 2 == 0]
    groups = {
        "C12": [[(x + y) % 12 for y in range(N)] for x in range(N)],
        "C3 x C2 x C2": [[4*((x//4 + y//4) % 3) + ((x%4) ^ (y%4))
                          for y in range(N)] for x in range(N)],
        "A4": [[even.index(tuple(p[i] for i in q)) for q in even] for p in even],
    }
    for name, square in (("D12", 0), ("Dic3", 3)):
        # x = r^i s^u,  r^6 = 1,  sr = r^(-1)s,  s^2 = r^square.
        table = []
        for x in range(N):
            u, i = divmod(x, 6)
            row = []
            for y in range(N):
                v, j = divmod(y, 6)
                row.append(6*((u+v) % 2) + (i + (-1)**u*j + square*u*v) % 6)
            table.append(row)
        groups[name] = table
    return groups


def automorphisms(mul):
    """All automorphisms by images of a generating list."""
    elements, words, generators = [0], [()], []
    while len(elements) < N:
        generators.append(next(g for g in range(N) if g not in elements))
        i = 0
        while i < len(elements):
            for k, g in enumerate(generators):
                value = mul[elements[i]][g]
                if value not in elements:
                    elements.append(value)
                    words.append(words[i] + (k,))
            i += 1
    for images in permutations(range(1, N), len(generators)):
        perm = [0]*N
        for x, word in zip(elements, words):
            value = 0
            for k in word:
                value = mul[value][images[k]]
            perm[x] = value
        if (len(set(perm)) == N and
                all(perm[mul[i][j]] == mul[perm[i]][perm[j]]
                    for i, j in product(range(N), repeat=2))):
            yield perm


def normalized_maps(right_difference):
    """Grow every f of distinct values with distinct f(x)x^(-1), f(0)=0."""
    maps = []

    def visit(prefix, values, differences):
        x = len(prefix)
        if x == N:
            maps.append(tuple(prefix))
            return
        for y in range(1, N):
            z = right_difference[y][x]
            if values & (1 << y) or differences & (1 << z):
                continue
            prefix.append(y)
            visit(prefix, values | (1 << y), differences | (1 << z))
            prefix.pop()

    visit([0], 1, 1)
    return maps


def representatives(maps, mul, left_difference, autos):
    remaining = set(maps)
    while remaining:
        f = min(remaining)
        orbit = set()
        for t in range(N):
            shifted = [left_difference[f[t]][f[mul[t][x]]] for x in range(N)]
            for auto in autos:
                g = [0]*N
                for x in range(N):
                    g[auto[x]] = auto[shifted[x]]
                orbit.add(tuple(g))
        assert orbit <= remaining
        remaining -= orbit
        yield f, len(orbit)


def slope_masks(maps, left_difference):
    # For each row pair and d, the set of indices with f(i)^(-1) f(j) = d.
    result = []
    for i, j in PAIRS:
        packs = [bytearray((len(maps)+7)//8) for _ in range(N)]
        for index, f in enumerate(maps):
            packs[left_difference[f[i]][f[j]]][index//8] |= 1 << (index%8)
        result.append(tuple(int.from_bytes(pack, "little") for pack in packs))
    return result


def cover_events(f, number_maps, left_difference, masks):
    choices = (1 << number_maps) - 1
    slopes = []
    for k, (i, j) in enumerate(PAIRS):
        slope = left_difference[f[i]][f[j]]
        choices &= ~masks[k][slope]
        slopes.append((left_difference[i][j], slope))
    events = []
    for k, excluded in enumerate(slopes):
        for d in range(1, N):
            if d not in excluded:
                event = choices & masks[k][d]
                if not event:
                    return None
                events.append(event)
    assert len(events) == 594
    return choices, events


def reject_last_orbit(choices, events):
    # Sum the pair equations after weighting them by their number of matches.
    weights = {4: -1, 5: 1, 6: 0, 7: 0, 8: 1, 12: 4}
    counts = Counter(event.bit_count() for event in events)
    assert counts == {4: 252, 5: 108, 6: 120, 7: 36, 8: 72, 12: 6}
    assert choices.bit_count() == 48
    assert sum(weights[d]*count*12 for d, count in counts.items()) == -576
    spectrum = Counter()
    while choices:
        bit = choices & -choices
        choices -= bit
        coeff = sum(weights[event.bit_count()] for event in events if event & bit)
        spectrum[coeff] += 1
    assert spectrum == {0: 30, 3: 12, 60: 6}


def check_group(name, mul, full):
    assert mul[0] == list(range(N)) and [row[0] for row in mul] == list(range(N))
    assert all(mul[mul[i][j]][k] == mul[i][mul[j][k]]
               for i, j, k in product(range(N), repeat=3))
    inverse = [row.index(0) for row in mul]
    left_difference = [[mul[inverse[i]][j] for j in range(N)] for i in range(N)]
    right_difference = [[mul[i][inverse[j]] for j in range(N)] for i in range(N)]
    maps = normalized_maps(right_difference)
    masks = slope_masks(maps, left_difference)
    orbit_count = exceptional = total_exceptional = 0
    for f, size in representatives(maps, mul, left_difference, list(automorphisms(mul))):
        orbit_count += 1
        event_data = cover_events(f, len(maps), left_difference, masks)
        if event_data is not None:
            reject_last_orbit(*event_data)
            exceptional += 1
            total_exceptional += size
    counts = (len(maps), orbit_count, exceptional, total_exceptional)
    assert counts == EXPECTED[name]
    if full:
        direct = 0
        for f in maps:
            event_data = cover_events(f, len(maps), left_difference, masks)
            if event_data is not None:
                reject_last_orbit(*event_data)
                direct += 1
        assert direct == total_exceptional
    print(name, counts)


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run without -O so that all exact checks are enabled.")
    if sys.argv[1:] not in ([], ["--all-maps"]):
        raise SystemExit("Usage: python erdos723_group_pairs.py [--all-maps]")
    for group, table in group_tables().items():
        check_group(group, table, bool(sys.argv[1:]))
