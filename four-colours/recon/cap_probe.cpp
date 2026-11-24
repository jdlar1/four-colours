// C++20. Ternary digit i is the colour at terminal i, clockwise from spoke 0.
#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cstdint>
#include <ctime>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

using namespace std;
using Matching = vector<pair<int, int>>;

struct Probe {
    int k, rim;
    array<int, 15> power{1};
    vector<int> inward, rimColour, tag, representatives;
    vector<uint8_t> live, mono;
    vector<uint32_t> blocks; // length followed by (canonical word ID * 3 + omitted colour)

    explicit Probe(const string &pattern) {
        if (pattern.size() != 5)
            throw invalid_argument("expected five gap sizes");
        rim = 0;
        for (char c : pattern) {
            if (c < '2' || c > '9')
                throw invalid_argument("gap outside 2..9");
            inward.push_back(rim);
            rim += c - '0';
        }
        k = rim - 5;
        if (k > 14)
            throw invalid_argument("maximum ring size is 14");
        rimColour.resize(rim);
        for (int i = 1; i <= k; ++i)
            power[i] = 3 * power[i - 1];
        tag.assign(power[k], -1);
        for (int code = 0; code < power[k]; ++code) {
            if (tag[code] >= 0)
                continue;
            array<int, 3> weight{}, count{};
            for (int i = 0, v = code; i < k; ++i, v /= 3) {
                weight[v % 3] += power[i];
                ++count[v % 3];
            }
            if ((count[0] % 2 != k % 2) || (count[1] % 2 != k % 2))
                continue;
            array<int, 3> perm{0, 1, 2};
            int id = representatives.size();
            representatives.push_back(code);
            mono.push_back(count[0] == k); // first numeric representative of monochrome orbit
            do {
                int target = 0, omit = 0;
                for (int c = 0; c < 3; ++c) {
                    target += perm[c] * weight[c];
                    if (perm[c] == 2)
                        omit = c;
                }
                tag[target] = 3 * id + omit;
            } while (next_permutation(perm.begin(), perm.end()));
        }
        live.assign(representatives.size(), 1);
    }

    void fill(int pos) {
        if (pos < rim) {
            for (int c = 0; c < 3; ++c) {
                // All names equivalent. Fix the first two rim edge colours.
                if ((pos < 2 && c != pos) || (pos && c == rimColour[pos - 1]) ||
                    (pos + 1 == rim && c == rimColour[0]))
                    continue;
                rimColour[pos] = c;
                fill(pos + 1);
            }
            return;
        }
        array<int, 5> spokes{};
        array<int, 3> count{};
        int code = 0, terminals = 0, s = 0;
        for (int i = 0; i < rim; ++i) {
            int c = 3 - rimColour[i] - rimColour[(i + rim - 1) % rim];
            if (s < 5 && inward[s] == i) {
                spokes[s++] = c;
                ++count[c];
            } else
                code += c * power[terminals++];
        }
        for (int i = 0; i < 5; ++i)
            if (count[spokes[i]] == 1 && count[spokes[(i + 1) % 5]] == 1) {
                live.at(tag.at(code) / 3) = 0;
                return;
            }
    }

    vector<Matching> matchings(int mask) const {
        if (!mask)
            return {Matching{}};
        int i = countr_zero((unsigned)mask);
        mask ^= 1 << i;
        vector<Matching> out;
        for (int choices = mask; choices; choices &= choices - 1) {
            int j = countr_zero((unsigned)choices);
            int inside = mask & ((1 << j) - 1);
            if (popcount((unsigned)inside) % 2)
                continue;
            auto right = matchings(mask ^ inside ^ (1 << j));
            for (auto &left : matchings(inside))
                for (auto &tail : right) {
                    out.push_back(left);
                    auto &m = out.back();
                    m.insert(m.end(), tail.begin(), tail.end());
                    m.emplace_back(i, j);
                }
        }
        return out;
    }

    void buildBlocks() {
        // The inactive terminals are C. A signed pair can have equal or
        // different endpoints. Choices of orientation are exactly path swaps.
        for (int active = 0; active < (1 << k); ++active) {
            if (popcount((unsigned)active) % 2)
                continue;
            int inactive = 0;
            for (int i = 0; i < k; ++i)
                if (!(active & (1 << i)))
                    inactive += 2 * power[i];
            for (const auto &m : matchings(active)) {
                int paths = m.size();
                for (int sign = 0; sign < (1 << paths); ++sign) {
                    if (popcount((unsigned)sign) % 2 != k % 2)
                        continue;
                    int code = inactive;
                    array<int, 7> step{};
                    for (int p = 0; p < paths; ++p) {
                        auto [i, j] = m[p];
                        bool different = sign & (1 << p);
                        if (different)
                            code += power[j];
                        step[p] = power[i] + (different ? -power[j] : power[j]);
                    }
                    // Complementary orientations differ by a global A/B swap.
                    int length = 1 << max(0, paths - 1);
                    size_t start = blocks.size();
                    blocks.push_back(length);
                    for (int s = 0; s < length; ++s) {
                        if (s) {
                            int bit = countr_zero((unsigned)s);
                            code += ((s >> (bit + 1)) & 1) ? -step[bit] : step[bit];
                        }
                        int t = tag.at(code);
                        if (t < 0)
                            throw logic_error("signed matching parity");
                        if (!live[t / 3]) {
                            blocks.resize(start);
                            break;
                        }
                        blocks.push_back(t);
                    }
                }
            }
        }
    }

    int sweep() {
        vector<uint8_t> supported(live.size(), 0);
        size_t write = 0;
        for (size_t p = 0; p < blocks.size();) {
            size_t end = p + 1 + blocks[p];
            bool all = true;
            for (size_t i = p + 1; i < end; ++i)
                if (!live[blocks[i] / 3]) {
                    all = false;
                    break;
                }
            if (all) {
                blocks[write++] = blocks[p];
                for (size_t i = p + 1; i < end; ++i) {
                    unsigned t = blocks[i];
                    supported[t / 3] |= 1u << (t % 3);
                    blocks[write++] = t;
                }
            }
            p = end;
        }
        blocks.resize(write);
        int removed = 0;
        for (size_t i = 0; i < live.size(); ++i) {
            if (mono[i] && (supported[i] & 6))
                supported[i] |= 6;
            if (live[i] && supported[i] != 7) {
                live[i] = 0;
                ++removed;
            }
        }
        return removed;
    }

    void run(const string &pattern, const char *output) {
        fill(0);
        cout << pattern << " classes " << live.size() << " direct "
             << count(live.begin(), live.end(), 0);
        buildBlocks();
        cout << " rounds";
        while (int removed = sweep())
            cout << ' ' << removed;
        cout << " survivors " << count(live.begin(), live.end(), 1);
        if (output) {
            ofstream out(output);
            out.exceptions(ios::badbit | ios::failbit);
            for (size_t i = 0; i < live.size(); ++i)
                if (live[i]) {
                    int v = representatives[i];
                    for (int j = 0; j < k; ++j, v /= 3)
                        out << char('A' + v % 3);
                    out << '\n';
                }
        }
    }
};

int main(int argc, char **argv) try {
    if (argc < 2 || argc > 3)
        throw invalid_argument("usage: cap_probe GAPS [survivor-file]");
    auto start = chrono::steady_clock::now();
    Probe(argv[1]).run(argv[1], argc == 3 ? argv[2] : nullptr);
    double elapsed = chrono::duration<double>(chrono::steady_clock::now() - start).count();
    // VmHWM belongs to this executable image. Linux ru_maxrss can also
    // include the high-water mark of the launcher before exec.
    ifstream status("/proc/self/status");
    string field;
    long peak = 0;
    while (status >> field) {
        if (field == "VmHWM:") {
            status >> peak;
            break;
        }
        string rest;
        getline(status, rest);
    }
    if (!peak)
        throw runtime_error("Linux VmHWM unavailable");
    cout << " elapsed_s " << elapsed << " cpu_s " << double(clock()) / CLOCKS_PER_SEC
         << " peak_KiB " << peak << '\n';
} catch (const exception &e) {
    cerr << e.what() << '\n';
    return 1;
}
