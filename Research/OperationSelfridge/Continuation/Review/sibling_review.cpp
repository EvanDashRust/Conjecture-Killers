#include <algorithm>
#include <array>
#include <iostream>
#include <vector>

// Upper bound for the maximum common weight of all root-to-leaf paths.
// Tokens at a level in different subtrees may share a numerical label,
// except that the second level has at most one occurrence of the pure power.
constexpr int max_budget = 17;
using Bounds = std::array<int, max_budget + 1>;
using Triple = std::array<int, 3>;

int maximize(const std::vector<int>& weights, int k, int i, Triple& sums,
             const std::vector<int>& prefix, int best) {
    if (i == k)
        return std::max(best, *std::min_element(sums.begin(), sums.end()));
    int need = 0;
    for (auto value : sums)
        need += std::max(0, best+1-value);
    if (need > prefix[k]-prefix[i])
        return best;
    for (int slot = 0; slot < 3; ++slot) {
        if (std::find(sums.begin(), sums.begin()+slot, sums[slot]) != sums.begin()+slot)
            continue;
        sums[slot] += weights[i];
        best = maximize(weights, k, i+1, sums, prefix, best);
        sums[slot] -= weights[i];
    }
    return best;
}

int level(const std::vector<int>& weights, int budget, const Bounds& first,
          const Bounds& second, const Bounds& third, int lower) {
    std::vector<int> prefix{0};
    for (auto w : weights)
        prefix.push_back(prefix.back()+w);
    int optimum = lower;
    for (int k = 0; k <= budget; ++k) {
        for (int a = 0; a <= budget-k; ++a) {
            for (int b = 0; b <= budget-k-a; ++b) {
                int c = budget-k-a-b;
                Triple sums{first[a],second[b],third[c]};
                optimum = maximize(weights,k,0,sums,prefix,optimum);
            }
        }
    }
    return optimum;
}

int main() {
    std::vector<int> weights;
    int w;
    while (std::cin >> w) weights.push_back(w);
    if (weights.size() < max_budget + 1) return 1;
    std::vector<int> shifted(weights.begin()+1,weights.end());
    Bounds unrestricted{}, no_pure{}, once{};
    for (int b = 1; b <= max_budget; ++b) {
        unrestricted[b] = level(weights,b,unrestricted,unrestricted,unrestricted,unrestricted[b-1]);
        no_pure[b] = level(shifted,b,unrestricted,unrestricted,unrestricted,no_pure[b-1]);
        once[b] = level(weights,b,unrestricted,no_pure,no_pure,once[b-1]);
        std::cout << b << ' ' << unrestricted[b] << ' ' << no_pure[b] << ' ' << once[b] << '\n';
    }
}
