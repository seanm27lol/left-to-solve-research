// Reproduce the complete largest-gap certificate for h = 2, 4, ..., 24.
// Build with g++ -std=c++17 -O3 cheb_gap24_clean.cpp -o cheb_gap24
// The largest modulus is below 2^56. Products of moduli fit in signed __int128.
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <vector>

#ifdef NDEBUG
#error "Compile with assertions enabled."
#endif

using Integer = std::int64_t;
using WideInteger = __int128_t;

struct Signs {
    int lower;
    int upper;
};

struct Counts {
    Integer compatible_pairs;
    Integer possible_cofactors;
    Integer prime_triples;
};

Integer prime_bound(Integer gap, bool same_sign) {
    const Integer square = gap * gap;
    if (same_sign) {
        const Integer multiplier = square * (square - 1) * (square - 1);
        return 1 + multiplier + 18 * square;
    }
    return 6 * square * square;
}

std::vector<bool> sieve(int limit) {
    std::vector<bool> prime(limit + 1, true);
    prime[0] = prime[1] = false;
    for (int factor = 2; factor <= limit / factor; ++factor) {
        if (prime[factor]) {
            for (int multiple = factor * factor; multiple <= limit; multiple += factor) {
                prime[multiple] = false;
            }
        }
    }
    return prime;
}

Integer modular_inverse(Integer value, Integer modulus) {
    Integer remainder = value % modulus;
    Integer next_remainder = modulus;
    WideInteger coefficient = 1;
    WideInteger next_coefficient = 0;
    while (next_remainder != 0) {
        const Integer quotient = remainder / next_remainder;
        const Integer reduced_remainder = remainder % next_remainder;
        const WideInteger reduced_coefficient = coefficient - quotient * next_coefficient;
        remainder = next_remainder;
        next_remainder = reduced_remainder;
        coefficient = next_coefficient;
        next_coefficient = reduced_coefficient;
    }
    assert(remainder == 1);
    coefficient %= modulus;
    if (coefficient < 0) {
        coefficient += modulus;
    }
    return static_cast<Integer>(coefficient);
}

// Extract the smallest prime divisor, then the smallest divisor of its cofactor.
// Strict inequalities enforce distinct factors, all at least seven and below p.
bool has_prime_triple(WideInteger cofactor, Integer p, const std::vector<bool>& prime) {
    if (cofactor % 2 == 0 || cofactor % 3 == 0 || cofactor % 5 == 0) {
        return false;
    }
    for (Integer a = 7; a < p && WideInteger(a) * a * a < cofactor; a += 2) {
        if (cofactor % a != 0) {
            continue;
        }
        assert(prime[a]);
        const WideInteger remaining = cofactor / a;
        if (remaining % a == 0) {
            return false;
        }
        for (Integer b = a + 2; b < p && WideInteger(b) * b <= remaining; b += 2) {
            if (remaining % b != 0) {
                continue;
            }
            assert(prime[b]);
            const WideInteger c = remaining / b;
            return b < c && c < p && prime[static_cast<Integer>(c)];
        }
        return false;
    }
    return false;
}

void check_pair(Integer p, Integer q, Signs signs, const std::vector<bool>& prime, Counts& counts) {
    const Integer first_modulus = p * (p - signs.lower);
    const Integer second_modulus = q * (q - signs.upper);
    // qX = s (mod p(p-s)) and pX = t (mod q(q-t)) require inverses.
    if (std::gcd(q, first_modulus) > 1 || std::gcd(p, second_modulus) > 1) {
        return;
    }
    const Integer first_residue =
        (signs.lower * modular_inverse(q, first_modulus) + first_modulus) % first_modulus;
    const Integer second_residue =
        (signs.upper * modular_inverse(p, second_modulus) + second_modulus) % second_modulus;
    const Integer common = std::gcd(first_modulus, second_modulus);
    const Integer difference = second_residue - first_residue;
    if (difference % common != 0) {
        return;
    }
    ++counts.compatible_pairs;

    // Generalized CRT, with the least nonnegative adjustment to the first residue.
    const Integer reduced = second_modulus / common;
    WideInteger adjustment = WideInteger(difference / common)
        * modular_inverse(first_modulus / common, reduced) % reduced;
    if (adjustment < 0) {
        adjustment += reduced;
    }
    const WideInteger first = first_residue + WideInteger(first_modulus) * adjustment;
    const WideInteger period = WideInteger(first_modulus) * reduced;
    const WideInteger upper_bound = WideInteger(p) * p * p;
    for (WideInteger x = first == 0 ? period : first; x < upper_bound; x += period) {
        assert(x % first_modulus == first_residue && x % second_modulus == second_residue);
        ++counts.possible_cofactors;
        if (has_prime_triple(x, p, prime)) {
            ++counts.prime_triples;
        }
    }
}

int main() {
    constexpr int largest_gap = 24;
    constexpr std::array<Integer, 12> expected_pairs{
        14, 208, 1982, 3459, 12939, 46887, 60637, 98739, 361294, 415009, 568938, 1618562};
    constexpr std::array<Integer, 12> expected_cofactors{1, 3, 4, 4, 5, 11, 4, 7, 5, 6, 2, 7};
    constexpr std::array<Signs, 3> signs_to_check{{{1, 1}, {-1, 1}, {1, -1}}};
    const auto prime = sieve(static_cast<int>(prime_bound(largest_gap, true)) + largest_gap);
    std::cout << "gap  compatible_signed_pairs  possible_cofactors  residual_prime_triples\n";

    for (int gap = 2; gap <= largest_gap; gap += 2) {
        Counts counts{};
        for (const Signs signs : signs_to_check) {
            // The global mixed-twin lemma excludes the negative-first twin case.
            // The reciprocal sum excludes two largest negatives for every gap.
            if (gap == 2 && signs.lower == -1) {
                continue;
            }
            const Integer bound = prime_bound(gap, signs.lower == signs.upper);
            for (Integer p = 7; p < bound; p += 2) {
                const Integer q = p + gap;
                if (prime[p] && prime[q]) {
                    check_pair(p, q, signs, prime, counts);
                }
            }
        }
        const int index = gap / 2 - 1;
        assert(counts.compatible_pairs == expected_pairs[index]);
        assert(counts.possible_cofactors == expected_cofactors[index]);
        assert(counts.prime_triples == 0);
        std::cout << gap << ' ' << counts.compatible_pairs << ' '
                  << counts.possible_cofactors << ' ' << counts.prime_triples << '\n';
    }
    std::cout << "Verified: the two largest primes differ by at least 26.\n";
}
