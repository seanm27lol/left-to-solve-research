// Independent direct sort. Generates ALL products a^3 b^4 c^5, including duplicates.
#include <algorithm>
#include <cstdint>
#include <iostream>
#include <vector>

int main() {
    using Word = std::uint64_t;
    using Wide = __uint128_t;
    constexpr Word limit = 10000000000000000000ULL + 1;
    std::vector<Word> values;
    for (Word c=1; ; ++c) {
        Wide five = Wide(c)*c*c*c*c;
        if (five > limit) break;
        for (Word b=1; ; ++b) {
            Wide scale = five*b*b*b*b;
            if (scale > limit) break;
            for (Word a=1; ; ++a) {
                Wide value = scale*a*a*a;
                if (value > limit) break;
                values.push_back(Word(value));
            }
        }
    }
    std::sort(values.begin(),values.end());
    auto total = values.size();
    values.erase(std::unique(values.begin(),values.end()), values.end());
    Word pairs = 0;
    for (size_t i=1;i<values.size();++i) {
        pairs += values[i] == values[i-1]+1;
    }
    std::cout<<"direct through 10^19+1: products "<<total<<"; distinct "<<values.size()
             <<"; adjacent pairs "<<pairs<<'\n';
    return pairs != 0;
}
