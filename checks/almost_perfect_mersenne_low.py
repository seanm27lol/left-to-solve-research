"""Exclude 2 <= t <= 20 in the three-prime Mersenne branch by exact division."""
from math import isqrt


def verify():
    tested = 0
    for t in range(2, 21):
        level = 2**t
        p = 2*level - 1
        if any(p % k == 0 for k in range(3, isqrt(p) + 1, 2)):
            continue
        # (r-p-1)(s-p-1) <= p(p+1) and s>r give r <= 2p+1.
        for r in range(p + 2, 2*p + 2, 2):
            tested += 1
            c = level*p*p*r*r
            b = (level - 1)*(p*p + p + 1)*(r*r + r + 1)
            f = c - b
            if f <= 0:
                continue
            # The positive component remainder D satisfies 0 < D/f < 1/(s+1).
            s = c // f
            assert s <= r or b*(s*s + s + 1) != c*s*s - 1
    return tested


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run with assertions enabled.")
    print(f"Excluded every small level over {verify():,} ordered prefixes.")
