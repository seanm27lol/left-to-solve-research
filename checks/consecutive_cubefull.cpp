// Reproduce with g++ -std=c++17 -O3 consecutive_cubefull.cpp -o /tmp/cubefull && /tmp/cubefull 24
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <string>
#include <vector>

using Word = std::uint64_t;
using Integer = __uint128_t;

Integer cube(Word n) { return Integer(n) * n * n; }

Word cube_root(Integer n) {
    Word root = std::cbrt(static_cast<long double>(n));
    while (cube(root + 1) <= n) ++root;
    while (cube(root) > n) --root;
    return root;
}

struct Family {
    Integer scale;
    Word last;
};

class FingerprintFilter {
    unsigned index_bits;
    Word mask;
    std::vector<Word> bits;

    static Word mix(Word z) {
        z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
        z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
        return z ^ (z >> 31);
    }
    static Word hash(Integer v) {
        return mix(Word(v) ^ mix(Word(v >> 64)));
    }

public:
    explicit FingerprintFilter(unsigned width) : index_bits(width), mask((Word(1)<<width)-1), bits((Word(1)<<width)/64,0) {}
    void add(Integer v) {
        Word h = hash(v), i = h & mask, j = (h >> (64-index_bits)) & mask;
        bits[i/64] |= Word(1) << (i%64);
        bits[j/64] |= Word(1) << (j%64);
    }
    bool maybe(Integer v) const {
        Word h = hash(v), i = h & mask, j = (h >> (64-index_bits)) & mask;
        return (bits[i/64] & (Word(1) << (i%64))) && (bits[j/64] & (Word(1) << (j%64)));
    }
};

std::vector<Family> make_families(Integer limit) {
    Word bound = 1;
    while (Integer(bound+1)*(bound+1)*(bound+1)*(bound+1) <= limit) ++bound;
    std::vector<bool> squarefree(bound + 1, true);
    for (Word p=2; p*p <= bound; ++p)
        for (Word k=p*p; k<=bound; k+=p*p) squarefree[k] = false;
    std::vector<Family> result;
    for (Word c=1; cube(c)*c*c <= limit; ++c) {
        if (!squarefree[c]) continue;
        Integer c5 = cube(c)*c*c, upper = limit/c5;
        for (Word b=1; cube(b)*b <= upper; ++b) {
            if (!squarefree[b] || std::gcd(b,c) != 1) continue;
            Integer scale = cube(b)*b*c5;
            result.push_back({scale,cube_root(limit/scale)});
        }
    }
    return result;
}

template<class Callback>
void odd_anchors(const std::vector<Family>& families, Integer limit, Callback take) {
    for (auto f : families) {
        if ((f.scale & 1) == 0) continue;
        // For odd a, a^3 is a modulo 8. Only residues 1,7 abut a multiple of 8.
        for (Word r=1; r<8; r+=2) {
            Word residue = (Word(f.scale) * r) % 8;
            if (residue != 1 && residue != 7) continue;
            for (Word a=r; a <= f.last; a+=8) {
                Integer odd = f.scale * cube(a);
                Integer e = residue == 1 ? odd-1 : odd+1;
                if (e != 0 && e <= limit) take(e,odd);
            }
        }
    }
}

std::string decimal(Integer n) {
    std::string s;
    do { s.push_back(char('0'+n%10)); n/=10; } while (n);
    std::reverse(s.begin(),s.end());
    return s;
}

int main(int argc, char** argv) {
    unsigned power = argc == 2 ? std::stoul(argv[1]) : 24;
    if (power == 0 || power > 26) throw std::invalid_argument("Choose an exponent 1 through 26.");
    Integer limit = 1;
    for (unsigned i=0; i<power; ++i) limit *= 10;
    auto families = make_families(limit+1);
    Word all = 0, evens = 0, odd_keys = 0;
    for (auto f : families) all += f.last;

    unsigned width = power <= 12 ? 20 : power <= 24 ? 29 : 31;
    FingerprintFilter odd_filter(width);
    odd_anchors(families,limit,[&](Integer e, Integer) { odd_filter.add(e); ++odd_keys; });

    FingerprintFilter even_filter(width);
    std::vector<Integer> candidates;
    for (auto f : families) {
        Word step = (f.scale & 1) != 0 ? 2 : 1;
        for (Word a=step; a<=f.last; a+=step) {
            Integer even = f.scale*cube(a);
            ++evens;
            if (!odd_filter.maybe(even)) continue;
            candidates.push_back(even);
            even_filter.add(even);
        }
    }
    std::sort(candidates.begin(),candidates.end());
    Word pairs = 0;
    odd_anchors(families,limit,[&](Integer e,Integer odd) {
        if (even_filter.maybe(e) && std::binary_search(candidates.begin(),candidates.end(),e)) {
            ++pairs;
            std::cout << "pair " << decimal(std::min(e,odd)) << ' ' << decimal(std::max(e,odd)) << '\n';
        }
    });
    std::cout << "n <= 10^" << power << "; families " << families.size()
              << "; cubefull positive terms <= 10^" << power << "+1: " << all
              << "; even terms " << evens << "; odd anchors " << odd_keys
              << "; filtered even terms " << candidates.size() << "; consecutive pairs " << pairs << '\n';
    if (pairs) return 1;
    return 0;
}
