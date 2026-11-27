// C++17 and compiler support for integer __int128. All arithmetic is exact.
// Run with assertions enabled. No bounds on the five integer factors are imposed.
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <vector>

using Integer = std::uint64_t;
using Wide = __uint128_t;
using SignedWide = __int128_t;

Integer power_mod(Integer a, Integer exponent, Integer modulus) {
    Integer result = 1;
    while (exponent != 0) {
        if (exponent % 2 == 1) result = Wide(result) * a % modulus;
        a = Wide(a) * a % modulus;
        exponent /= 2;
    }
    return result;
}

bool prime(Integer n) {
    // The least strong pseudoprime to the first seven prime bases is
    // 341550071728321. See https://arxiv.org/pdf/1207.0063, p. 2.
    assert(n >= 2 && n < 341550071728321ULL);
    Integer odd = n - 1;
    int valuation = 0;
    while (odd % 2 == 0) {
        odd /= 2;
        ++valuation;
    }
    for (Integer base : {2, 3, 5, 7, 11, 13, 17}) {
        if (n % base == 0) return n == base;
        Integer residue = power_mod(base, odd, n);
        if (residue == 1 || residue == n - 1) continue;
        bool passed = false;
        for (int j = 1; j < valuation; ++j) {
            residue = Wide(residue) * residue % n;
            if (residue == n-1) {
                passed = true;
                break;
            }
        }
        if (!passed) return false;
    }
    return true;
}

Integer proper_factor(Integer n) {
    // Pollard rho is used only to find a divisor. Each return value
    // is an exact gcd strictly between one and n.
    for (Integer constant = 1; ; ++constant) {
        Integer slow = 2, fast = 2, divisor = 1;
        auto advance = [&](Integer x) {
            return static_cast<Integer>((Wide(x)*x + constant) % n);
        };
        while (divisor == 1) {
            slow = advance(slow);
            fast = advance(advance(fast));
            divisor = std::gcd(std::max(slow,fast)-std::min(slow,fast), n);
        }
        if (divisor != n) return divisor;
    }
}

void factorize(Integer n, std::vector<Integer>& factors) {
    if (n == 1) return;
    if (prime(n)) {
        factors.push_back(n);
        return;
    }
    const Integer divisor = proper_factor(n);
    factorize(divisor, factors);
    factorize(n/divisor, factors);
}

void populate_divisors(Integer n, std::vector<Integer>& divisors) {
    std::vector<Integer> factors;
    for (Integer p : {2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97}) {
        while (n % p == 0) {
            factors.push_back(p);
            n /= p;
        }
    }
    factorize(n, factors);
    std::sort(factors.begin(), factors.end());
    divisors.assign(1, 1);
    for (size_t i = 0; i < factors.size();) {
        const auto old_size = divisors.size();
        const Integer p = factors[i];
        Integer power = 1;
        do {
            power *= p;
            ++i;
            for (size_t j = 0; j < old_size; ++j) divisors.push_back(power*divisors[j]);
        } while (i < factors.size() && factors[i] == p);
    }
}

Integer square_root(Wide x) {
    Wide left = 0, right = Wide(1) << 64;
    while (right-left > 1) {
        const Wide mid = (left+right)/2;
        if (mid*mid <= x) left=mid;
        else right=mid;
    }
    return static_cast<Integer>(left);
}

int main() {
#ifdef NDEBUG
#error "Compile without -DNDEBUG to verify the certificate."
#endif
    constexpr Integer max_gap = 500;
    std::vector<Integer> divisors;
    std::array<Integer,6> counts{};
    for (Integer v = 2; v <= max_gap; v += 2) {
        for (Integer j = 3; j < 4*v; j += 2) {
            for (Integer k = 1; k < j && j+k < 4*v; k += 2) {
                const Integer m = j+k, u=j*k, C=u+2*m+4;
                if (m <= v || std::gcd(v,std::gcd(m,u)) > 1) continue;
                ++counts[0];
                const Integer W = v*C*C-m-4;
                assert(W%2 == 0 && W/2 < 341550071728321ULL);
                populate_divisors(W/2,divisors);
                const SignedWide X = SignedWide(v)*(u*(j-k))*(u*(j-k))-m*m*m;
                for (Integer divisor : divisors) {
                    const Integer d = 2*divisor-1;
                    if (d < 7 || d <= j+v) continue;
                    const SignedWide M = SignedWide(m)*d-u;
                    if (X % M != 0) continue;
                    ++counts[1];
                    // Checked for every divisor hit, before forming Q.
                    assert(d < 1000000);
                    const Wide Q = Wide(d)*(2*d-j)*(2*d-k);
                    const Wide numerator = v*Q+1;
                    if (numerator % M != 0) continue;
                    ++counts[2];
                    const Wide Y = numerator/M, H=Y+v-1;
                    const Wide discriminant = v*v + 4*Y;
                    const Integer root = square_root(discriminant);
                    if (Wide(root)*root == discriminant) ++counts[5];
                    const Integer diff_sq = (v-2)*(v-2);
                    const Wide g_sq = diff_sq == 0 ? H :
                        std::gcd(static_cast<Integer>(H % diff_sq), diff_sq);
                    const Integer g = square_root(g_sq);
                    if (Wide(g)*g != g_sq) continue;
                    ++counts[3];
                    if (((v-1)*Q+1) % (H/g) == 0) ++counts[4];
                }
            }
        }
    }
    std::cout << "Gap triples, divisor hits, integral products, square gcds, shift survivors, square discriminants:\n";
    for (auto value : counts) std::cout << value << " ";
    std::cout << "\n";
    const std::array<Integer,6> expected = {18627549, 507, 49, 31, 0, 0};
    assert(counts == expected);
}
