// Read a stream of plantri -P10c2m2 planar_code records (one header).
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
using namespace std;

using Mask = unsigned;
constexpr int ring = 10, limit = 16;
array<uint8_t, 1 << 20> bad; // packed two-bit nonzero edge differences

struct Disk {
    int n;
    array<Mask, limit> adjacent{}, colouredNeighbours{};
    array<array<int, limit>, limit> rotation{};
    array<int, limit> degree{}, order{}, colour{};
    array<int, ring> outer{};
    array<Mask, 4> used{};
    int failed = 0;

    explicit Disk(int size) : n(size) {
        if (n < ring || n >= limit)
            throw runtime_error("unexpected vertex count");
        for (int i = 0; i < n; ++i) {
            int c;
            while ((c = cin.get()) != 0) {
                if (c < 1 || c > n || degree[i] >= n)
                    throw runtime_error("invalid planar_code");
                int j = c - 1;
                rotation[i][degree[i]++] = j;
                adjacent[i] |= 1u << j;
            }
        }
        // plantri roots its oriented edge 0->1 on the distinguished face.
        bool found = false;
        for (int turn : {1, -1}) {
            int u = 0, v = 1;
            for (int step = 0; step < ring; ++step) {
                outer[step] = u;
                int j = 0;
                while (j < degree[v] && rotation[v][j] != u)
                    ++j;
                if (j == degree[v])
                    throw runtime_error("asymmetric edge");
                int w = rotation[v][(j + degree[v] + turn) % degree[v]];
                u = v;
                v = w;
                if (u == 0 && v == 1) {
                    found = step + 1 == ring;
                    break;
                }
            }
            if (found)
                break;
        }
        if (!found)
            throw runtime_error("invalid decagon face");
    }

    void prepare() {
        Mask done = 0;
        for (int i = 0; i < n; ++i) {
            int best = -1, score = -1;
            for (int v = 0; v < n; ++v)
                if (!(done & (1u << v))) {
                    int s = 16 * popcount(done & adjacent[v]) + degree[v];
                    if (s > score) {
                        score = s;
                        best = v;
                    }
                }
            order[i] = best;
            colouredNeighbours[i] = done & adjacent[best];
            done |= 1u << best;
        }
    }

    void search(int pos, int names) {
        if (pos == n) {
            int packed = 0;
            for (int i = 0; i < ring; ++i)
                packed |= (colour[outer[i]] ^ colour[outer[(i + 1) % ring]]) << (2 * i);
            failed |= bad[packed];
            return;
        }
        int v = order[pos];
        for (int c = 0; c < min(4, names + 1) && failed != 3; ++c) {
            if (used[c] & colouredNeighbours[pos])
                continue;
            colour[v] = c;
            used[c] ^= 1u << v;
            search(pos + 1, max(names, c + 1));
            used[c] ^= 1u << v;
        }
    }
};

int main(int argc, char **argv) try {
    if (argc != 2)
        throw runtime_error("usage: plantri -P10c2m2 n | disk_probe survivor-file");
    ifstream input(argv[1]);
    string word;
    int countWords = 0;
    while (input >> word) {
        if (word.size() != ring)
            throw runtime_error("bad boundary length");
        array<int, 3> p{1, 2, 3};
        do {
            int a = 0, b = 0;
            for (int i = 0; i < ring; ++i) {
                a |= p.at(word[i] - 'A') << (2 * i);
                b |= p.at(word[(i + 1) % ring] - 'A') << (2 * i);
            }
            bad[a] |= 1;
            bad[b] |= 2;
        } while (next_permutation(p.begin(), p.end()));
        ++countWords;
    }
    if (countWords != 1220)
        throw runtime_error("expected 1220 canonical survivors");
    ios::sync_with_stdio(false);
    cin.tie(nullptr);
    string header(15, ' ');
    cin.read(header.data(), header.size());
    if (header != ">>planar_code<<")
        throw runtime_error("missing planar_code header");
    long total = 0, passes = 0;
    int n;
    while ((n = cin.get()) != EOF) {
        Disk disk(n);
        ++total;
        disk.prepare();
        disk.search(0, 0);
        if (disk.failed != 3) {
            ++passes;
            if (passes == 1)
                cout << "first_passing_disk " << total << " failed_alignment_mask " << disk.failed
                     << '\n';
        }
    }
    cout << "disks " << total << " passing_disks " << passes << '\n';
} catch (const exception &e) {
    cerr << e.what() << '\n';
    return 1;
}
