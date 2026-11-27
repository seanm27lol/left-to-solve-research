"""Upper-bound the eligible reciprocal weights for either Chebyshev sign.

Python 3.9+, standard library. Run without -O. All rounding is upward and
uses integers. At d | M, an odd prime p <= C is eligible for sign s when

    gcd(p-s, M) | d,       p does not divide d,       p+s does not divide d.

The returned score is K*T + sum over eligible p of (ceil(Q/p)-T),
where M=lcm(1,...,B), Q=10^12 and T=ceil(Q/C). This bounds Q times a
sum of at most K eligible reciprocals if primes above C are also allowed:
each contributes at most T units, and each eligible prime <=C can supply
its nonnegative excess over T at most once. Scores can overcount actual
prime factors. The main calculation retains even divisors d.
"""

from math import gcd, isqrt, lcm


Q = 10**12
B = 48
C = 30_000_000
K = 2_000_000
EXPECTED = {
    1: (979_992_270_359, 852_921_110_814_300),
    -1: (984_946_515_023, 1_283_847_370_696_800),
}


def ceil_ratio(numerator, denominator):
    return (numerator + denominator - 1) // denominator


def prime_sieve(limit):
    sieve = bytearray([1]) * (limit + 1)
    sieve[:2] = bytes(2)
    for prime in range(2, isqrt(limit) + 1):
        if sieve[prime]:
            first = prime * prime
            sieve[first::prime] = bytes((limit - first) // prime + 1)
    return sieve


def modulus_and_divisors(bound, flags):
    """Factor lcm(1,...,bound) and form each of its positive divisors once."""
    divisors = [1]
    factors = []
    modulus = 1
    for prime in range(2, bound + 1):
        if not flags[prime]:
            continue
        factors.append(prime)
        powers = [1]
        while powers[-1] * prime <= bound:
            powers.append(powers[-1] * prime)
        modulus *= powers[-1]
        divisors = [d * power for d in divisors for power in powers]
    assert modulus == lcm(*range(1, bound+1))
    return modulus, sorted(divisors), factors


def all_scores(sign, budget, cutoff, modulus, divisors, factors, flags):
    """Accumulate four divisibility events and sum them over divisors."""
    baseline = ceil_ratio(Q, cutoff)
    events = dict.fromkeys(divisors, 0)
    for p in range(3, cutoff + 1, 2):
        if not flags[p]:
            continue
        excess = ceil_ratio(Q, p) - baseline
        required = gcd(p - sign, modulus)
        events[required] += excess

        # Remove d divisible by p and d divisible by the whole forbidden
        # shift p+s. Such d can only exist when the indicated factor divides M.
        # Add back the intersection to avoid removing it twice. As p divides
        # neither p-s nor p+s, the lcm with p is simply multiplication by p.
        if modulus % p == 0:
            events[required * p] -= excess
        if modulus % (p + sign) == 0:
            both_shifts = lcm(required, p + sign)
            events[both_shifts] -= excess
            if modulus % p == 0:
                events[both_shifts * p] += excess

    # Each d should receive every event indexed by a divisor of d. Taking
    # prefix sums in each prime exponent does exactly this. Numerical order
    # visits d/prime before d, so repeated powers are accumulated in one pass.
    for prime in factors:
        for d in divisors:
            if d % prime == 0:
                events[d] += events[d // prime]
    return {d: budget * baseline + value for d, value in events.items()}


def direct_score(d, sign, budget, cutoff, modulus, primes):
    """Independent evaluation of the defining predicate at a single divisor."""
    baseline = ceil_ratio(Q, cutoff)
    score = budget * baseline
    count = 0
    for p in primes:
        if d % gcd(p - sign, modulus) or d % p == 0 or d % (p + sign) == 0:
            continue
        count += 1
        score += ceil_ratio(Q, p) - baseline
    return score, count


def check_small():
    """Check all divisors and both signs against explicit eligible prime sets."""
    for bound, cutoff, budget in ((8, 31, 4), (10, 89, 17), (12, 173, 30)):
        flags = prime_sieve(cutoff)
        modulus, divisors, factors = modulus_and_divisors(bound, flags)
        # Enumerate divisors and primes independently of the efficient routines.
        assert divisors == [d for d in range(1, modulus+1) if modulus % d == 0]
        primes = [p for p in range(3, cutoff+1, 2)
                  if all(p % k for k in range(2, isqrt(p)+1))]
        assert primes == [p for p in range(3, cutoff+1, 2) if flags[p]]
        for sign in (1, -1):
            scores = all_scores(sign, budget, cutoff, modulus, divisors, factors, flags)
            for d in divisors:
                assert scores[d] == direct_score(d, sign, budget, cutoff, modulus, primes)[0]


def verify():
    check_small()
    flags = prime_sieve(C)
    modulus, divisors, factors = modulus_and_divisors(B, flags)
    assert len(divisors) == 294_912
    print(f"M={modulus}, {len(divisors)} divisors, T={ceil_ratio(Q, C)}")
    extended = 2_451_595
    margin = Q - max(score for score, _ in EXPECTED.values()) - (extended - K)*ceil_ratio(Q, C)
    assert margin == 17_247 and 3**17 * margin > Q
    for sign in (1, -1):
        scores = all_scores(sign, K, C, modulus, divisors, factors, flags)
        best = max(value for d, value in scores.items() if d % 2 == 0)
        winners = [d for d in divisors if d % 2 == 0 and scores[d] == best]
        expected_score, expected_winner = EXPECTED[sign]
        assert best == expected_score and winners == [expected_winner]
        for d in winners:
            odd_primes = (p for p in range(3, C+1, 2) if flags[p])
            exact, count = direct_score(d, sign, K, C, modulus, odd_primes)
            assert exact == best
            print(f"sign={sign:+d} maximum={best} d={d} eligible_odd_primes={count}")
        print(f"maximizing_divisors={len(winners)}")


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run without -O so all assertions are active.")
    verify()
