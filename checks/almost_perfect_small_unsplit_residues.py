"""Check the even-level unsplit-largest branch at all residues with absolute value at most 12."""


def enumerate_residues():
    radius = 12
    counts = [0] * 3
    for a in range(-radius, radius + 1):
        if abs(a) < 2:
            continue
        A = 1 + abs(a)
        f = a*a + a + 1
        for k in range(11, (6000 * A**16 - 1).bit_length()):
            U = 1 << k
            assert U >= 2*A*A
            q = U*U-1
            # Here q is vastly larger than 2*abs(a).
            for L in range(1+(a%2), min(8*A**3, 2*U) + 1, 2):
                counts[0] += 1
                v = a - L
                w = (v+1) * pow(v*v+v+1, -1, 2*U) % (2*U)
                m = abs(U-w)
                if m == 0 or m == U or L*m > 4*U:
                    continue
                eps = 1 if w<U else -1
                counts[1] += 1
                z = a*(m*f+eps*(a+1))
                if (z*z-1) % q:
                    continue
                counts[2] += 1
    assert counts == [3660032, 16946, 0], counts
    return counts

if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run without -O to check the certificate.")
    print(enumerate_residues())
