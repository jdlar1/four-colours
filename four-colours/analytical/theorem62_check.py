#!/usr/bin/env python3
"""Sanity checks for analytical/theorem62_proof.md (Theorem 6.2: Kempe spans = Birkhoff-Lewis span).

Single-threaded, numpy only, k <= 9, a few seconds.  Run:  python3 theorem62_check.py
Every check is an assert; the script prints a table and ends with "ALL CHECKS PASSED".

Conventions (as in thrust2_memo.md / the proof):
  * word t in {1,2,3}^k, XOR(t)=0; edge j (0-based) joins ring vertices j and j+1 (mod k);
    vertex colours c[0]=0, c[j]=t[0]^...^t[j-1]  (c in {0,1,2,3} = F_2^2, a=bit0, b=bit1).
  * palette alpha: sector S = {j : t_j != alpha}; y_j = [t_j == gamma] (gamma = fixed other letter).
  * B_alpha = span of Kempe (signed noncrossing matching) block indicators, computed here as
    span{ chi_U|sector : U subset of S balanced }  (Lemma 2 of the proof), and checked against
    the literal block indicators for k <= 6.
"""
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "NUMEXPR_NUM_THREADS"):
    os.environ[_v] = "1"
import itertools
import math
import time

import numpy as np

TOL = 1e-9


# ---------------------------------------------------------------- combinatorics
def central_trinomial(k):
    return sum(math.comb(k, 2 * m) * math.comb(2 * m, m) for m in range(k // 2 + 1))


def dim_formula(k):  # (T_k + (-1)^k)/2
    return (central_trinomial(k) + (-1) ** k) // 2


def riordan(k):  # A005043: R_0=1, R_1=0, (n+1)R_n = (n-1)(2R_{n-1} + 3R_{n-2})
    R = [1, 0]
    for n in range(2, k + 1):
        R.append((n - 1) * (2 * R[n - 1] + 3 * R[n - 2]) // (n + 1))
    return R[k]


def words(k):
    return [t for t in itertools.product((1, 2, 3), repeat=k) if np.bitwise_xor.reduce(t) == 0]


def colours(t):
    c = [0]
    for x in t[:-1]:
        c.append(c[-1] ^ x)
    return c


def nc_partitions(pts):
    """All noncrossing partitions of the points pts (in circular order), each exactly once."""
    pts = tuple(pts)
    if not pts:
        yield []
        return

    def grow(block, pos):
        for P in nc_partitions(pts[pos:]):          # block of pts[0] ends here
            yield [tuple(block)] + P
        for q in range(pos, len(pts)):              # next element of the block is pts[q]
            for P1 in nc_partitions(pts[pos:q]):
                for P2 in grow(block + [pts[q]], q + 1):
                    yield P1 + P2

    yield from grow([pts[0]], 1)


def nc_matchings(pts):
    pts = list(pts)
    if not pts:
        yield []
        return
    a = pts[0]
    for i in range(1, len(pts), 2):
        for L in nc_matchings(pts[1:i]):
            for R in nc_matchings(pts[i + 1:]):
                yield [(a, pts[i])] + L + R


def balanced(mask, n):
    return sum((-1) ** i for i in range(n) if mask >> i & 1) == 0


def popparity(x):
    return bin(x).count("1") & 1


# ---------------------------------------------------------------- palette spans
class Palette:
    """Orthonormal basis of B_alpha, block-diagonal over sectors."""

    def __init__(self, W, alpha):
        k = len(W[0])
        beta, gamma = [x for x in (1, 2, 3) if x != alpha]
        groups = {}
        for i, t in enumerate(W):
            S = tuple(j for j in range(k) if t[j] != alpha)
            y = sum(1 << l for l, j in enumerate(S) if t[j] == gamma)
            groups.setdefault(S, []).append((i, y))
        self.sectors, self.loc, off = [], {}, 0
        for S, lst in groups.items():
            n2 = len(S)
            reps = [U for U in range(1 << n2) if not U & 1 and balanced(U, n2)] if n2 else [0]
            idx = np.array([i for i, _ in lst])
            ys = [y for _, y in lst]
            H = np.array([[(-1) ** popparity(U & y) for y in ys] for U in reps], float) / math.sqrt(len(ys))
            assert np.allclose(H @ H.T, np.eye(len(reps)))       # distinct complement-pairs orthogonal
            self.sectors.append((idx, H, off))
            for col, i in enumerate(idx):
                self.loc[i] = (len(self.sectors) - 1, col)
            off += len(reps)
        self.dim = off

    def residual(self, V):
        """max |V - proj_{B_alpha} V| for V of shape (n, p)."""
        r = 0.0
        for idx, H, _ in self.sectors:
            Vs = V[idx]
            r = max(r, np.abs(Vs - H.T @ (H @ Vs)).max())
        return r

    def dense(self, n):
        Q = np.zeros((self.dim, n))
        for idx, H, off in self.sectors:
            Q[off:off + H.shape[0], idx] = H
        return Q


def cap_dim(P1, P2, n):
    """dim(B1 ∩ B2) from singular values of Q1 Q2^T (built sparsely: a palette-1 sector and a
    palette-2 sector share at most one word)."""
    M = np.zeros((P1.dim, P2.dim))
    for i in range(n):
        s1, j1 = P1.loc[i]
        s2, j2 = P2.loc[i]
        _, H1, o1 = P1.sectors[s1]
        _, H2, o2 = P2.sectors[s2]
        M[o1:o1 + H1.shape[0], o2:o2 + H2.shape[0]] += np.outer(H1[:, j1], H2[:, j2])
    sv = np.linalg.svd(M, compute_uv=False)
    d = int((sv > 1 - 1e-8).sum())
    gap = sv[d] if d < len(sv) else 0.0
    return d, gap


def kempe_blocks(W, idx, alpha):
    """Literal signed noncrossing-matching block indicators (slow; small k only)."""
    k = len(W[0])
    beta, gamma = [x for x in (1, 2, 3) if x != alpha]
    seen, vecs = set(), []
    for t in W:
        S = [j for j in range(k) if t[j] != alpha]
        for M in nc_matchings(S):
            key = (tuple(S), tuple(M), tuple(t[a] == t[b] for a, b in M))
            if key in seen:
                continue
            seen.add(key)
            v = np.zeros(len(W))
            for flips in itertools.product((0, 1), repeat=len(M)):
                u = list(t)
                for f, (a, b) in zip(flips, M):
                    if f:
                        u[a] = beta + gamma - u[a]
                        u[b] = beta + gamma - u[b]
                v[idx[tuple(u)]] = 1
            vecs.append(v)
    return np.array(vecs)


def rank(A):
    if A.shape[0] == 0:
        return 0
    s = np.linalg.svd(A, compute_uv=False)
    return int((s > TOL * max(1.0, s[0])).sum())


def null_basis(A):
    """Orthonormal basis (rows) of the null space of A, via eigh of A^T A."""
    w, v = np.linalg.eigh(A.T @ A)
    return v[:, w < 1e-9 * max(1.0, w[-1])].T


def cap_dense(Q1, Q2):
    if Q1.shape[0] == 0 or Q2.shape[0] == 0:
        return 0
    return int((np.linalg.svd(Q1 @ Q2.T, compute_uv=False) > 1 - 1e-8).sum())


# ---------------------------------------------------------------- per-k checks on W_k
def check_words(k, full_kempe):
    W = words(k)
    n = len(W)
    idx = {t: i for i, t in enumerate(W)}
    assert n == (3 ** k + 3 * (-1) ** k) // 4
    pal = [Palette(W, a) for a in (1, 2, 3)]
    for P in pal:
        assert P.dim == dim_formula(k), (k, P.dim)
    if full_kempe:   # Lemma 2: Kempe block span == balanced-character span
        for a, P in zip((1, 2, 3), pal):
            Bk = kempe_blocks(W, idx, a)
            assert rank(Bk) == P.dim and P.residual(Bk.T) < 1e-9
    # Birkhoff-Lewis vectors zeta_sigma, sigma NC with no cyclically adjacent pair in a block
    NC = list(nc_partitions(range(k)))
    assert len(NC) == math.comb(2 * k, k) // (k + 1)
    Rk = [p for p in NC if not any((x + 1) % k in b for b in p for x in b if len(b) > 1)]
    assert len(Rk) == riordan(k)
    C = np.array([colours(t) for t in W])
    Z = np.zeros((len(Rk), n))
    for r, p in enumerate(Rk):
        ok = np.ones(n, bool)
        for b in p:
            for x in b[1:]:
                ok &= C[:, x] == C[:, b[0]]
        Z[r] = ok
    sz = np.linalg.svd(Z, compute_uv=False)            # 0/1 matrix: s_min ~ 0.1, noise ~ 1e-13
    assert sz[-1] > 1e-8 * sz[0]                        # zeta_sigma independent: rank BL = R_k
    res = max(P.residual(Z.T) for P in pal)            # BL ⊆ B_1 ∩ B_2 ∩ B_3
    assert res < 1e-9
    d12, gap = cap_dim(pal[0], pal[1], n)               # dim(B_1 ∩ B_2)
    assert d12 == len(Rk), (k, d12, len(Rk))
    d13 = "-"                                            # redundant by S_3 symmetry; ~2s at k=9
    if k <= 8:
        d13, _ = cap_dim(pal[0], pal[2], n)
        assert d13 == len(Rk), (k, d13, len(Rk))
    return dict(k=k, words=n, dimB=pal[0].dim, cap12=d12, cap13=d13, R=len(Rk), res=res, gap=gap,
                pal=pal, W=W, idx=idx)


def inv(w):
    return sum(1 for i in range(len(w)) for j in range(i + 1, len(w)) if w[i] > w[j])


def check_uncertainty(D):
    """N_k = {F : E_v f = 0 on proper colourings}: explicit form, N∩B1, N∩B1∩B2 = 0."""
    k, W, idx, pal = D["k"], D["W"], D["idx"], D["pal"]
    n = len(W)
    rows = []
    for t in W:
        for j in range(k):
            j2 = (j + 1) % k
            r = np.zeros(n)
            if t[j] != t[j2]:                              # (A)
                u = list(t); u[j], u[j2] = t[j2], t[j]
                r[idx[t]] += 1; r[idx[tuple(u)]] += 1
            else:                                          # (S)
                for z in (1, 2, 3):
                    u = list(t); u[j] = u[j2] = z
                    r[idx[tuple(u)]] += 1
            rows.append(r)
    A = np.array(rows)
    N = null_basis(A)
    dimN = (k // 2 + 1) if k % 2 == 0 else (k - 1) // 2
    assert N.shape[0] == dimN, (k, N.shape[0])
    # explicit: F = (-1)^inv g(content), sum_r g(nu + 2 e_r) = 0
    cont = [(t.count(1), t.count(2), t.count(3)) for t in W]
    cl = sorted(set(cont))
    E = np.zeros((len(cl), n))
    for i, t in enumerate(W):
        E[cl.index(cont[i]), i] = (-1) ** inv(t)
    nus = sorted({(c[0] - 2 * (r == 0), c[1] - 2 * (r == 1), c[2] - 2 * (r == 2))
                  for c in cl for r in range(3)})
    nus = [v for v in nus if min(v) >= 0]
    Rel = np.array([[1.0 if any(tuple(v[i] + 2 * (i == r) for i in range(3)) == c for r in range(3)) else 0.0
                     for c in cl] for v in nus]) if nus else np.zeros((0, len(cl)))
    G = null_basis(Rel) if Rel.shape[0] else np.eye(len(cl))
    Nexp = G @ E
    assert np.abs(A @ Nexp.T).max() < 1e-9 and rank(np.vstack([N, Nexp])) == dimN
    Q1, Q2 = pal[0].dense(n), pal[1].dense(n)
    nb1 = cap_dense(N, Q1)
    assert nb1 == (1 if k % 2 == 0 else 0)
    # N ∩ B1 ∩ B2 = 0: any vector of N ∩ B1 (at most 1-dim) is not in B2
    if nb1:
        K = k // 2
        Df = lambda j: math.prod(range(1, 2 * j, 2))      # (2j-1)!!
        Aseq = [1.0]
        for j in range(K):
            Aseq.append(-2 * (K - j) * Aseq[-1])
        F = np.array([(-1) ** inv(t) * Aseq[c[0] // 2] * Df(c[1] // 2) * Df(c[2] // 2)
                      for t, c in zip(W, cont)])
        F /= np.linalg.norm(F)
        assert np.abs(A @ F).max() < 1e-9                  # explicit element of N_k
        assert pal[0].residual(F[:, None]) < 1e-9          # ... lies in B_1
        assert pal[1].residual(F[:, None]) > 1e-3          # ... but not in B_2
    return N.shape[0], nb1


# ---------------------------------------------------------------- free setting (4^k colourings)
def check_free(k):
    nc_ = 4 ** k
    a = np.array([[(c >> (2 * v)) & 1 for v in range(k)] for c in range(nc_)])
    b = np.array([[(c >> (2 * v + 1)) & 1 for v in range(k)] for c in range(nc_)])
    amask = (a << np.arange(k)).sum(1)
    bmask = (b << np.arange(k)).sum(1)

    def matchable(Y, x):          # Y bitmask, x: 0/1 letters on vertices (bitmask)
        ys = [v for v in range(k) if Y >> v & 1]
        return len(ys) % 2 == 0 and sum((-1) ** l * (x >> y & 1) for l, y in enumerate(ys)) == 0

    def basis(first, second):     # [second = x0] chi_Y(first), Y x0-matchable
        rows = []
        for x0 in range(1 << k):
            sel = (second == x0)
            for Y in range(1 << k):
                if matchable(Y, x0):
                    par = np.array([popparity(Y & m) for m in first])
                    rows.append(np.where(sel, (-1.0) ** par, 0.0))
        Q = np.array(rows)
        return Q / np.linalg.norm(Q, axis=1, keepdims=True)

    Q1, Q2 = basis(amask, bmask), basis(bmask, amask)
    assert Q1.shape[0] == Q2.shape[0] == math.comb(2 * k, k)
    col = a + 2 * b
    L = []
    for p in nc_partitions(range(k)):
        ok = np.ones(nc_, bool)
        for blk in p:
            for x in blk[1:]:
                ok &= col[:, x] == col[:, blk[0]]
        L.append(ok.astype(float))
    L = np.array(L)
    cat = math.comb(2 * k, k) // (k + 1)
    assert rank(L) == cat
    for Q in (Q1, Q2):
        assert np.abs(L - (L @ Q.T) @ Q).max() < 1e-9      # Lfrak ⊆ Bfrak_1 ∩ Bfrak_2
    X = cap_dense(Q1, Q2)
    assert X == cat, (k, X, cat)
    return Q1.shape[0], X


# ---------------------------------------------------------------- Q=4 chromatic joins / Rumer
def check_joins(k):
    NC = list(nc_partitions(range(k)))

    def join_count(p, q):
        parent = list(range(k))

        def f(x):
            while parent[x] != x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x
        for blk in p + q:
            for x in blk[1:]:
                parent[f(x)] = f(blk[0])
        return len({f(x) for x in range(k)})

    def matching(p):              # boundary NC matching on 2k points: (2i+1) -- 2*next(i)
        m = {}
        for blk in p:
            for i, x in enumerate(blk):
                y = blk[(i + 1) % len(blk)]
                m[2 * x + 1] = 2 * y
                m[2 * y] = 2 * x + 1
        return m

    mats = [matching(p) for p in NC]
    assert len({tuple(sorted(m.items())) for m in mats}) == len(NC)
    G = np.zeros((len(NC), len(NC)))
    for i, p in enumerate(NC):
        for j, q in enumerate(NC):
            mp, mq = mats[i], mats[j]
            seen, loops = set(), 0                          # meander loops of (m(p), m(q))
            for s in range(2 * k):
                if s in seen:
                    continue
                loops += 1
                x, use_p = s, True
                while x not in seen:
                    seen.add(x)
                    x = mp[x] if use_p else mq[x]
                    seen.add(x)
                    x = mq[x] if use_p else mp[x]
            J = join_count(p, q)
            assert loops == 2 * J + k - len(p) - len(q)
            G[i, j] = 4.0 ** J
    ev = np.linalg.eigvalsh(G)
    assert ev[0] > 0                                         # chromatic-joins matrix at Q=4 is PD
    return ev[0] / ev[-1]


# ---------------------------------------------------------------- main
if __name__ == "__main__":
    t0 = time.time()
    for k in range(1, 13):                                   # closed form / generating function
        T = [central_trinomial(j) for j in range(k + 1)]
        if k >= 2:
            assert k * T[k] == (2 * k - 1) * T[k - 1] + 3 * (k - 1) * T[k - 2]
        assert dim_formula(k) == sum(math.comb(k, 2 * m) * math.comb(2 * m, m) // 2
                                     for m in range(1, k // 2 + 1)) + (k % 2 == 0)
    print("dim B_alpha = (T_k+(-1)^k)/2 :", {k: dim_formula(k) for k in range(2, 12)})
    print(" k  words  dimB  dim(B1∩B2) dim(B1∩B3)  R_k  BL-resid   next-sv  dimN  dim(N∩B1)  N∩B1∩B2")
    for k in range(2, 10):
        D = check_words(k, full_kempe=(k <= 6))
        dN, nb1 = check_uncertainty(D) if k <= 7 else ("-", "-")
        print(f"{k:2d} {D['words']:6d} {D['dimB']:5d} {D['cap12']:9d} {D['cap13']!s:>10} {D['R']:6d}"
              f"  {D['res']:.1e}  {D['gap']:.3f}  {dN!s:>4}  {nb1!s:>8}  {'0' if k <= 7 else '-':>6}")
    for k in range(1, 6):
        dB, X = check_free(k)
        print(f"free k={k}: dim Bfrak_1 = {dB} = C(2k,k), dim(Bfrak_1 ∩ Bfrak_2) = {X} = Catalan = dim Lfrak")
    for k in range(1, 7):
        r = check_joins(k)
        print(f"joins k={k}: loops = 2#(s v t)+k-|s|-|t| ok; Gram 4^#(s v t) PD (cond^-1 {r:.2e})")
    print(f"ALL CHECKS PASSED  ({time.time() - t0:.1f}s)")
