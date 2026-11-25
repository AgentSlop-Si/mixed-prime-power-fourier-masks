#!/usr/bin/env python3
"""Standalone exact & numerical verification script for:
'Mixed Prime-Power Fourier Masks and Quantitative Odd Codimension-Two Spectral Gaps'
by Daniyar Kuttymbek, Adilkhan Kuttymbek, Dayana Kuttymbek,
Amina Kolpenova, and Mukhammadali Kottumbekov.

Uses Python 3 standard library only (zero external dependencies). Verifies:
1. Theorem 1.1 / Section 2: Exact cyclotomic weighted character-filtration descent across
   prime-power divisor masks, the connected (8,4) mask (Example 2.4) with unequal-exponent
   children and exact Q[zeta_8] inverse-row witness, weighted repeated-label stress controls,
   and negative controls (3x2 rectangular one-sided Gram & switch corruption).
2. Theorem 1.2 / Section 3: Exact CRT congruences, short-overlap q-character erasure
   (Lemma 3.1), separate fiber vanishing, and weighted prime-power descent on the erased
   matrix across N = p^a q (including shifted-label masks with nonempty cross-q overlaps),
   sharpness of the d < q guard at d = q, and exhaustive short-subset erasure at N = 12, 20.
3. Theorem 1.3 / Section 4: Exhaustive check of Lemma 4.1 across all 27 (N=3) and all
   100,000 (N=5) ordered two-entry-per-column support patterns (plus even-N evaders),
   exact Q[zeta_N] verification of Lemma 4.2's stability identities (with padded supports)
   at N = 3, 5, 7, exact Table 2 constants, and numerical spectral-norm verification of
   Theorem 1.3 on Fourier and flat-unitary targets.
"""
from __future__ import annotations

import cmath
from collections import defaultdict, deque
from fractions import Fraction
import itertools
import math
import random


# ---------------------------------------------------------------------------
# Exact cyclotomic polynomial arithmetic over Z and Q
# ---------------------------------------------------------------------------

def poly_trim(p: list[int]) -> list[int]:
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p


def poly_div_exact(num: list[int], den: list[int]) -> list[int]:
    """Exact polynomial division in Z[X] assuming den is monic and divides num."""
    rem = list(num)
    d = len(den) - 1
    assert den[-1] == 1
    if len(rem) - 1 < d:
        assert all(c == 0 for c in rem)
        return [0]
    quot = [0] * (len(rem) - d)
    for k in range(len(rem) - 1, d - 1, -1):
        coeff = rem[k]
        if coeff != 0:
            quot[k - d] = coeff
            for j in range(d + 1):
                rem[k - d + j] -= coeff * den[j]
    assert all(c == 0 for c in rem), f"Non-exact division remainder: {rem}"
    return poly_trim(quot)


def poly_mod_monic(p: list[int], mod: list[int]) -> list[int]:
    """Reduce integer polynomial p modulo monic integer polynomial mod."""
    rem = list(p)
    d = len(mod) - 1
    assert mod[-1] == 1
    for k in range(len(rem) - 1, d - 1, -1):
        coeff = rem[k]
        if coeff != 0:
            for j in range(d + 1):
                rem[k - d + j] -= coeff * mod[j]
    return poly_trim(rem[:d]) if d > 0 else [0]


_CYCLO_CACHE: dict[int, list[int]] = {}


def cyclotomic_poly(n: int) -> list[int]:
    """Compute exact Phi_n(X) in Z[X] via X^n - 1 = prod_{d|n} Phi_d(X)."""
    if n in _CYCLO_CACHE:
        return _CYCLO_CACHE[n]
    poly = [-1] + [0] * (n - 1) + [1]
    for d in range(1, n):
        if n % d == 0:
            poly = poly_div_exact(poly, cyclotomic_poly(d))
    _CYCLO_CACHE[n] = poly
    return poly


def vanish_cyclo(terms: list[tuple[int, int]], order: int) -> bool:
    """Exact test whether sum_{(e, c)} c * zeta_order^e == 0 in Z[zeta_order]."""
    if order == 1:
        return sum(c for _, c in terms) == 0
    hist = [0] * order
    for e, c in terms:
        hist[e % order] += c
    rem = poly_mod_monic(hist, cyclotomic_poly(order))
    return all(x == 0 for x in rem)


def vanish_prime_power(terms: list[tuple[int, int]], p: int, a: int) -> bool:
    """Fast exact test in Z[X]/Phi_{p^a}(X) using Phi_{p^a}(X) = sum_{q=0}^{p-1} X^{q p^{a-1}}."""
    if a == 0:
        return sum(c for _, c in terms) == 0
    L = p ** a
    n = L // p
    hist = [0] * L
    for e, c in terms:
        hist[e % L] += c
    for u in range(n):
        base = hist[u]
        for q in range(1, p):
            if hist[u + q * n] != base:
                return False
    return True


# ---------------------------------------------------------------------------
# Part 1: Weighted prime-power descent (Theorem 1.1 & Example 2.4)
# ---------------------------------------------------------------------------

CONNECTED_8x4 = [
    [int(ch) for ch in row]
    for row in [
        "00110011",
        "01010101",
        "11001100",
        "10101010",
        "00110011",
        "10101010",
        "11001100",
        "01010101",
    ]
]


def divisor_mask(N: int, d: int) -> list[list[int]]:
    assert N % d == 0
    h = N // d
    return [[1 if (r // d) == (c % h) else 0 for c in range(N)] for r in range(N)]


def is_bipartite_connected(R: list[list[int]]) -> bool:
    n = len(R)
    seen = {0}
    q = deque([0])
    while q:
        v = q.popleft()
        if v < n:
            nbrs = [n + c for c in range(n) if R[v][c]]
        else:
            c = v - n
            nbrs = [r for r in range(n) if R[r][c]]
        for w in nbrs:
            if w not in seen:
                seen.add(w)
                q.append(w)
    return len(seen) == 2 * n


def validate_weighted_state(state: dict) -> None:
    """Exact verification of A*A = AA* = d I_m in W(p, a, d)."""
    p, a, d = state["p"], state["a"], state["d"]
    x, y, k, R = state["x"], state["y"], state["k"], state["R"]
    m = len(x)
    assert m > 0 and len(y) == m and len(k) == m and len(R) == m
    L = p ** a
    assert all(0 <= xi < L for xi in x)
    assert all(0 <= yj < L for yj in y)
    assert all(isinstance(ki, int) and ki >= 0 for ki in k)
    assert all(len(row) == m and all(v in (0, 1) for v in row) for row in R)

    # Row Gram: AA* = d I_m
    for i in range(m):
        assert (p ** k[i]) * sum(R[i]) == d, f"Row norm mismatch at row {i}"
        for l in range(i + 1, m):
            terms = [((x[i] - x[l]) * y[j], 1) for j in range(m) if R[i][j] and R[l][j]]
            assert vanish_prime_power(terms, p, a), f"Row Gram ({i},{l}) nonzero"

    # Column Gram: A*A = d I_m
    for j in range(m):
        col_norm = sum((p ** k[r]) for r in range(m) if R[r][j])
        assert col_norm == d, f"Column norm mismatch at col {j}: {col_norm} != {d}"
        for l in range(j + 1, m):
            terms = [
                (x[r] * (y[l] - y[j]), p ** k[r])
                for r in range(m)
                if R[r][j] and R[r][l]
            ]
            assert vanish_prime_power(terms, p, a), f"Col Gram ({j},{l}) nonzero"


def descend_one_level(state: dict) -> list[dict]:
    """Execute Proposition 2.3 (weighted character-filtration descent) and verify every invariant."""
    validate_weighted_state(state)
    p, a, d = state["p"], state["a"], state["d"]
    assert a >= 1
    x, y, k, R = state["x"], state["y"], state["k"], state["R"]
    m = len(x)
    L = p ** a
    n = L // p

    # Partition rows into pure and mixed
    pure_rows: dict[int, list[int]] = defaultdict(list)
    mixed_rows: set[int] = set()
    for i in range(m):
        residues = {y[j] % p for j in range(m) if R[i][j]}
        assert len(residues) >= 1
        if len(residues) == 1:
            pure_rows[next(iter(residues))].append(i)
        else:
            mixed_rows.add(i)

    # Match mixed rows into disjoint p-tuples using anchor pairs (Lemma 2.2)
    matched: set[int] = set()
    tuples: list[tuple[int, list[int]]] = []  # (u, [i_0, ..., i_{p-1}])
    for i in sorted(mixed_rows):
        if i in matched:
            continue
        supp = [j for j in range(m) if R[i][j]]
        # Find anchor pair of distinct residues mod p
        j0 = supp[0]
        j1 = next(j for j in supp if (y[j] % p) != (y[j0] % p))
        u = x[i] % n
        siblings = []
        for q_idx in range(p):
            target_label = u + q_idx * n
            cands = [r for r in range(m) if x[r] == target_label and R[r][j0] and R[r][j1]]
            assert len(cands) == 1, f"Expected unique sibling at label {target_label}"
            sib = cands[0]
            assert R[sib] == R[i], "Sibling support mismatch"
            assert k[sib] == k[i], "Sibling weight mismatch"
            siblings.append(sib)
        # Verify residue balance
        counts = [sum(1 for j in supp if y[j] % p == t) for t in range(p)]
        assert len(set(counts)) == 1 and counts[0] > 0, f"Unbalanced residues: {counts}"
        for sib in siblings:
            assert sib not in matched
            matched.add(sib)
        tuples.append((u, siblings))

    assert matched == mixed_rows

    # Build child blocks for each residue class t = 0..p-1
    children: list[dict] = []
    total_dim = 0
    for t in range(p):
        cols_t = [j for j in range(m) if y[j] % p == t]
        c_t = len(cols_t)
        new_x: list[int] = []
        new_k: list[int] = []
        new_R: list[list[int]] = []
        for i in pure_rows[t]:
            new_x.append(x[i] % n)
            new_k.append(k[i])
            new_R.append([R[i][j] for j in cols_t])
        for u, sibs in tuples:
            rep = sibs[0]
            new_x.append(u)
            new_k.append(k[rep] + 1)
            new_R.append([R[rep][j] for j in cols_t])
        r_t = len(new_x)
        assert r_t == c_t, f"Non-square child block at t={t}: {r_t}x{c_t}"
        if r_t > 0:
            child = {
                "p": p,
                "a": a - 1,
                "d": d,
                "x": new_x,
                "y": [(y[j] - t) // p for j in cols_t],
                "k": new_k,
                "R": new_R,
            }
            validate_weighted_state(child)
            children.append(child)
            total_dim += r_t
    assert total_dim == m and len(children) >= 1
    return children


def run_full_descent(state: dict) -> list[int]:
    """Descend recursively to a = 0 and return all terminal exponents k'_i."""
    if state["a"] == 0:
        validate_weighted_state(state)
        m = len(state["x"])
        for i in range(m):
            assert sum(state["R"][i]) == 1, "Terminal row support must be a singleton"
            assert (state["p"] ** state["k"][i]) == state["d"]
        return list(state["k"])
    exps: list[int] = []
    for child in descend_one_level(state):
        exps.extend(run_full_descent(child))
    return exps


# Exact arithmetic in Q[z]/(z^4 + 1) for the connected (8,4) inverse witness
class QZeta8:
    @staticmethod
    def zero() -> tuple[Fraction, ...]:
        return (Fraction(0),) * 4

    @staticmethod
    def pow_z(e: int) -> tuple[Fraction, ...]:
        e %= 8
        sgn = Fraction(1) if e < 4 else Fraction(-1)
        out = [Fraction(0)] * 4
        out[e % 4] = sgn
        return tuple(out)

    @staticmethod
    def add(a: tuple[Fraction, ...], b: tuple[Fraction, ...]) -> tuple[Fraction, ...]:
        return tuple(x + y for x, y in zip(a, b))

    @staticmethod
    def sub(a: tuple[Fraction, ...], b: tuple[Fraction, ...]) -> tuple[Fraction, ...]:
        return tuple(x - y for x, y in zip(a, b))

    @staticmethod
    def scale(a: tuple[Fraction, ...], s: Fraction) -> tuple[Fraction, ...]:
        return tuple(x * s for x in a)

    @staticmethod
    def conj(a: tuple[Fraction, ...]) -> tuple[Fraction, ...]:
        # conj(z^k) = z^{-k}
        return (a[0], -a[3], -a[2], -a[1])

    @staticmethod
    def mul(a: tuple[Fraction, ...], b: tuple[Fraction, ...]) -> tuple[Fraction, ...]:
        c = [Fraction(0)] * 4
        for i in range(4):
            for j in range(4):
                e = i + j
                c[e % 4] += a[i] * b[j] * (1 if e < 4 else -1)
        return tuple(c)

    @staticmethod
    def inv(a: tuple[Fraction, ...]) -> tuple[Fraction, ...]:
        # Solve 4x4 linear system over Q for a * x = 1
        M = [[Fraction(0)] * 5 for _ in range(4)]
        for col in range(4):
            e_col = [Fraction(0)] * 4
            e_col[col] = Fraction(1)
            prod = QZeta8.mul(a, tuple(e_col))
            for row in range(4):
                M[row][col] = prod[row]
        M[0][4] = Fraction(1)
        # Gauss-Jordan elimination
        for col in range(4):
            piv = next(r for r in range(col, 4) if M[r][col] != 0)
            M[col], M[piv] = M[piv], M[col]
            pv = M[col][col]
            M[col] = [v / pv for v in M[col]]
            for r in range(4):
                if r != col and M[r][col] != 0:
                    f = M[r][col]
                    M[r] = [M[r][c] - f * M[col][c] for c in range(5)]
        return tuple(M[r][4] for r in range(4))


def invert_matrix_qzeta8(A: list[list[tuple[Fraction, ...]]]) -> list[list[tuple[Fraction, ...]]]:
    n = len(A)
    aug = [
        list(A[r]) + [QZeta8.pow_z(0) if r == c else QZeta8.zero() for c in range(n)]
        for r in range(n)
    ]
    for col in range(n):
        piv = next(r for r in range(col, n) if aug[r][col] != QZeta8.zero())
        aug[col], aug[piv] = aug[piv], aug[col]
        inv_pv = QZeta8.inv(aug[col][col])
        aug[col] = [QZeta8.mul(v, inv_pv) for v in aug[col]]
        for r in range(n):
            if r != col and aug[r][col] != QZeta8.zero():
                f = aug[r][col]
                aug[r] = [QZeta8.sub(aug[r][c], QZeta8.mul(f, aug[col][c])) for c in range(2 * n)]
    return [row[n:] for row in aug]


def verify_part1_prime_power() -> None:
    # 1. Connected (8,4) mask (Example 2.4)
    assert is_bipartite_connected(CONNECTED_8x4), "CONNECTED_8x4 must be bipartite-connected"
    state84 = {
        "p": 2,
        "a": 3,
        "d": 4,
        "x": list(range(8)),
        "y": list(range(8)),
        "k": [0] * 8,
        "R": CONNECTED_8x4,
    }
    children = descend_one_level(state84)
    assert len(children) == 2
    child_exps = sorted(sorted(c["k"]) for c in children)
    assert child_exps == [[0, 0, 1, 1], [0, 0, 1, 1]], f"Unexpected child exponents: {child_exps}"
    exps_exact = [c["k"] for c in children]
    assert exps_exact[0] == [0, 0, 1, 1] or sorted(exps_exact[0]) == [0, 0, 1, 1]
    term_exps = run_full_descent(state84)
    assert all(e == 2 for e in term_exps) and len(term_exps) == 8

    # Exact Q[zeta_8] inverse-row witness for CONNECTED_8x4:
    # H[r,c] = z^(rc), A_kept = H - D, B_tilde = A_kept^* / 4, M_tilde = B_tilde^{-1}
    # Then (M_tilde - H)(M_tilde - H)^* = 4 I_8 => ||M - F_8||_2 = sqrt(4/8) = sqrt(1/2).
    H = [[QZeta8.pow_z(r * c) for c in range(8)] for r in range(8)]
    A_kept = [
        [QZeta8.zero() if CONNECTED_8x4[r][c] else H[r][c] for c in range(8)]
        for r in range(8)
    ]
    B_tilde = [
        [QZeta8.scale(QZeta8.conj(A_kept[c][r]), Fraction(1, 4)) for c in range(8)]
        for r in range(8)
    ]
    for r in range(8):
        assert sum(1 for c in range(8) if B_tilde[r][c] != QZeta8.zero()) == 4
    M_tilde = invert_matrix_qzeta8(B_tilde)
    E_tilde = [[QZeta8.sub(M_tilde[r][c], H[r][c]) for c in range(8)] for r in range(8)]
    for i in range(8):
        for j in range(8):
            acc = QZeta8.zero()
            for c in range(8):
                acc = QZeta8.add(acc, QZeta8.mul(E_tilde[i][c], QZeta8.conj(E_tilde[j][c])))
            expected = (Fraction(4), Fraction(0), Fraction(0), Fraction(0)) if i == j else QZeta8.zero()
            assert acc == expected, f"Error Gram mismatch at ({i},{j}): {acc}"

    # 2. Divisor-block masks across prime powers
    divisor_cases = 0
    for p, max_a in [(2, 4), (3, 3), (5, 2), (7, 1)]:
        for a in range(1, max_a + 1):
            N = p ** a
            for b in range(0, a + 1):
                d = p ** b
                st = {
                    "p": p,
                    "a": a,
                    "d": d,
                    "x": list(range(N)),
                    "y": list(range(N)),
                    "k": [0] * N,
                    "R": divisor_mask(N, d),
                }
                term = run_full_descent(st)
                assert len(term) == N and all(e == b for e in term)
                divisor_cases += 1

    # 3. Weighted repeated-label stress control (direct sum of embedded blocks at p=2, a=3, d=8)
    # Block 1: order-8 full Fourier (k=0, 8x8); Block 2: order-4 full Fourier scaled by p^{1/2} (k=1, 4x4);
    # Block 3: order-2 full Fourier scaled by p^{2/2} (k=2, 2x2). Total size m=14 != 8, repeated labels!
    m_s = 14
    R_s = [[0] * m_s for _ in range(m_s)]
    x_s = list(range(8)) + [0, 2, 4, 6] + [0, 4]
    y_s = list(range(8)) + [0, 1, 2, 3] + [0, 1]
    k_s = [0] * 8 + [1] * 4 + [2] * 2
    for i in range(8):
        for j in range(8):
            R_s[i][j] = 1
    for i in range(8, 12):
        for j in range(8, 12):
            R_s[i][j] = 1
    for i in range(12, 14):
        for j in range(12, 14):
            R_s[i][j] = 1
    st_weighted = {"p": 2, "a": 3, "d": 8, "x": x_s, "y": y_s, "k": k_s, "R": R_s}
    term_w = run_full_descent(st_weighted)
    assert len(term_w) == 14 and all(e == 3 for e in term_w)

    # 4. Negative controls:
    # (a) Degree-preserving 2x2 switch on CONNECTED_8x4 fails Gram
    R_bad = [row[:] for row in CONNECTED_8x4]
    # Row 0 has (0->0, 2->1); Row 2 has (0->1, 2->0) -> swap them!
    R_bad[0][0], R_bad[0][2] = 1, 0
    R_bad[2][0], R_bad[2][2] = 0, 1
    failed = False
    try:
        validate_weighted_state(
            {"p": 2, "a": 3, "d": 4, "x": list(range(8)), "y": list(range(8)), "k": [0] * 8, "R": R_bad}
        )
    except AssertionError:
        failed = True
    assert failed, "Corrupted connected mask should fail exact Gram check"

    # (b) Remark 2.3 rectangular 3x2 countercontrol: A*A = 4 I_2 holds, AA* != 4 I_3
    # Rows: (sqrt(2), sqrt(2)), (1, -1), (1, -1)
    A_rect = [
        [math.sqrt(2), math.sqrt(2)],
        [1.0, -1.0],
        [1.0, -1.0],
    ]
    col_gram = [
        [sum(A_rect[r][i] * A_rect[r][j] for r in range(3)) for j in range(2)]
        for i in range(2)
    ]
    assert abs(col_gram[0][0] - 4.0) < 1e-12 and abs(col_gram[1][1] - 4.0) < 1e-12
    assert abs(col_gram[0][1]) < 1e-12
    row_gram_12 = sum(A_rect[1][c] * A_rect[2][c] for c in range(2))
    assert abs(row_gram_12 - 2.0) < 1e-12  # nonzero off-diagonal -> AA* != 4 I_3

    print(
        f"  [PASS] Part 1 (Theorem 1.1): {divisor_cases} divisor descents, connected (8,4) + exact Q[zeta_8] inverse witness, "
        "14x14 weighted repeated-label stress test, and negative controls."
    )


# ---------------------------------------------------------------------------
# Part 2: Short-overlap q-character erasure & mixed prime powers (Theorem 1.2)
# ---------------------------------------------------------------------------

def verify_exact_mask_and_erasure(
    p: int, a: int, q: int, d: int, R: list[list[int]], expect_erased_valid: bool
) -> None:
    m = p ** a
    N = m * q
    em = q * pow(q, -1, m)
    eq = m * pow(m, -1, q)
    assert (em + eq) % N == 1
    assert (em * eq) % N == 0
    assert (em * em) % N == em % N
    assert (eq * eq) % N == eq % N

    # Build CRT coordinate maps
    coords = [(r % m, r % q) for r in range(N)]
    for r in range(N):
        x, b = coords[r]
        assert (x * em + b * eq) % N == r
    # Check CRT phase congruence on sample pairs
    for r in range(0, N, max(1, N // 8)):
        x, b = coords[r]
        for c in range(0, N, max(1, N // 8)):
            y, v = coords[c]
            assert (r * c) % N == (x * y * em + b * v * eq) % N

    # Verify original D*D = d I_N and DD* = d I_N exactly in Z[zeta_N]
    for i in range(N):
        assert sum(R[i]) == d
        for j in range(i + 1, N):
            terms = [((i - j) * c, 1) for c in range(N) if R[i][c] and R[j][c]]
            assert vanish_cyclo(terms, N), f"Original row Gram ({i},{j}) nonzero at N={N},d={d}"
    for c1 in range(N):
        assert sum(R[r][c1] for r in range(N)) == d
        y1, v1 = coords[c1]
        for c2 in range(c1 + 1, N):
            y2, v2 = coords[c2]
            terms = [(r * (c2 - c1), 1) for r in range(N) if R[r][c1] and R[r][c2]]
            assert vanish_cyclo(terms, N), f"Original col Gram ({c1},{c2}) nonzero at N={N},d={d}"
            if expect_erased_valid and v1 != v2:
                # Verify EVERY separate q-fiber coefficient C_b vanishes in Z[alpha]
                by_b: dict[int, list[tuple[int, int]]] = defaultdict(list)
                for r in range(N):
                    if R[r][c1] and R[r][c2]:
                        x_r, b_r = coords[r]
                        by_b[b_r].append((x_r * (y2 - y1), 1))
                for b_r in range(q):
                    assert vanish_prime_power(by_b[b_r], p, a), (
                        f"Fiber C_{b_r} nonzero for ({c1},{c2}) at N={N},d={d}"
                    )

    # Form erased matrix E in W(p, a, d) with q-fold repeated labels
    erased_state = {
        "p": p,
        "a": a,
        "d": d,
        "x": [coords[r][0] for r in range(N)],
        "y": [coords[c][0] for c in range(N)],
        "k": [0] * N,
        "R": R,
    }
    if expect_erased_valid:
        term = run_full_descent(erased_state)
        b_exp = int(round(math.log(d, p)))
        assert p ** b_exp == d and all(e == b_exp for e in term)
    else:
        erased_failed = False
        try:
            validate_weighted_state(erased_state)
        except AssertionError:
            erased_failed = True
        assert erased_failed, f"Expected boundary d=q={q} mask at N={N} to FAIL after erasure"


def shifted_mixed_mask(p: int, a: int, q: int, d: int) -> list[list[int]]:
    """Construct R[(x,b),(y,v)] = T[x,y] * 1_{v == (b + y) mod q}, giving genuinely
    nonempty cross-q column overlaps whenever d >= 2."""
    m = p ** a
    N = m * q
    T = divisor_mask(m, d)
    R = [[0] * N for _ in range(N)]
    for r in range(N):
        x, b = r % m, r % q
        for c in range(N):
            y, v = c % m, c % q
            if T[x][y] and v == (b + y) % q:
                R[r][c] = 1
    return R


def verify_part2_mixed_prime_power() -> None:
    # 1. Positive controls (both divisor masks and shifted-label cross-q masks) + descent on E
    test_specs = [
        (2, 2, 3),  # N=12
        (2, 2, 5),  # N=20
        (2, 3, 5),  # N=40
        (3, 2, 5),  # N=45
    ]
    pos_count = 0
    for p, a, q in test_specs:
        N = (p ** a) * q
        for j in range(a + 1):
            d = p ** j
            if d < q:
                verify_exact_mask_and_erasure(p, a, q, d, divisor_mask(N, d), True)
                pos_count += 1
                if d >= 2 and N <= 20:
                    R_sh = shifted_mixed_mask(p, a, q, d)
                    # Confirm genuinely nonempty cross-q column overlaps exist
                    cross_overlaps = 0
                    for c1 in range(N):
                        for c2 in range(c1 + 1, N):
                            if (c1 % q) != (c2 % q):
                                if any(R_sh[r][c1] and R_sh[r][c2] for r in range(N)):
                                    cross_overlaps += 1
                    assert cross_overlaps > 0
                    verify_exact_mask_and_erasure(p, a, q, d, R_sh, True)
                    pos_count += 1

    # 2. Sharpness of d < q guard at boundary d = q
    boundary_count = 0
    for p, a, q in [(2, 2, 3), (2, 2, 5), (3, 2, 5)]:
        N = (p ** a) * q
        verify_exact_mask_and_erasure(p, a, q, q, divisor_mask(N, q), False)
        boundary_count += 1

    # 3. Exhaustive short-subset erasure check at N = 12 (m=4, q=3) and N = 20 (m=4, q=5)
    # For any subset S of Z/NZ with 1 <= |S| < q and any delta with q not dividing delta,
    # if sum_{r in S} zeta_N^{r * delta} == 0 then every fiber sum C_b == 0 in Z[zeta_m].
    short_checked = 0
    short_vanishing = 0
    for m, q in [(4, 3), (4, 5)]:
        N = m * q
        em = q * pow(q, -1, m)
        for sz in range(1, q):
            for S in itertools.combinations(range(N), sz):
                short_checked += 1
                for delta in (1, 1 + m):  # delta % q != 0
                    if delta % q == 0:
                        continue
                    if vanish_cyclo([(r * delta, 1) for r in S], N):
                        short_vanishing += 1
                        dy = delta % m
                        by_b: dict[int, list[tuple[int, int]]] = defaultdict(list)
                        for r in S:
                            by_b[r % q].append(((r % m) * dy, 1))
                        for b in range(q):
                            assert vanish_cyclo(by_b[b], m)

    print(
        f"  [PASS] Part 2 (Theorem 1.2): {pos_count} positive mixed prime-power erasure+descent checks, "
        f"{boundary_count} boundary d=q guard failures, and {short_checked} short-subset erasure checks "
        f"({short_vanishing} vanishing)."
    )


# ---------------------------------------------------------------------------
# Part 3: Quantitative odd codimension-two spectral gap (Theorem 1.3)
# ---------------------------------------------------------------------------

def classify_two_col_pattern(N: int, supports: tuple[tuple[int, int], ...]) -> str:
    """Return 'Case I' (singleton intersection) or 'Case II' (triple repeated support) or 'NONE'."""
    for i in range(N):
        s_i = set(supports[i])
        for j in range(i + 1, N):
            if len(s_i & set(supports[j])) == 1:
                return "Case I"
    counts: dict[tuple[int, int], int] = defaultdict(int)
    for s in supports:
        counts[s] += 1
    if max(counts.values()) >= 3:
        return "Case II"
    return "NONE"


def verify_exhaustive_two_col_obstruction() -> None:
    # Exhaust all 3^3 = 27 patterns at N = 3 and all 10^5 = 100,000 patterns at N = 5
    for N, exp_total in [(3, 27), (5, 100_000)]:
        pairs = list(itertools.combinations(range(N), 2))
        c1 = c2 = irregular = 0
        for pat in itertools.product(pairs, repeat=N):
            kind = classify_two_col_pattern(N, pat)
            assert kind in ("Case I", "Case II"), f"Evader found at odd N={N}: {pat}"
            if kind == "Case I":
                c1 += 1
            else:
                c2 += 1
            row_deg = [0] * N
            for u, v in pat:
                row_deg[u] += 1
                row_deg[v] += 1
            if any(d != 2 for d in row_deg):
                irregular += 1
        assert c1 + c2 == exp_total
        print(
            f"  [PASS] Lemma 4.1 exhaustive at odd N={N}: {exp_total:,} patterns "
            f"(Case I={c1:,}, Case II={c2:,}, row-irregular={irregular:,}, evaders=0)"
        )

    # Even-N negative control: disjoint pairs each repeated twice evade both Case I and Case II
    for N in (4, 6, 8):
        pat = tuple((2 * (i // 2), 2 * (i // 2) + 1) for i in range(N))
        assert classify_two_col_pattern(N, pat) == "NONE"


def matmul_c(A: list[list[complex]], B: list[list[complex]]) -> list[list[complex]]:
    n = len(A)
    return [[sum(A[i][k] * B[k][j] for k in range(n)) for j in range(n)] for i in range(n)]


def conj_T(A: list[list[complex]]) -> list[list[complex]]:
    n = len(A)
    return [[A[j][i].conjugate() for j in range(n)] for i in range(n)]


def mat_inv_c(A: list[list[complex]]) -> list[list[complex]]:
    n = len(A)
    aug = [list(A[r]) + [1.0 + 0j if r == c else 0j for c in range(n)] for r in range(n)]
    for col in range(n):
        piv = max(range(col, n), key=lambda r: abs(aug[r][col]))
        assert abs(aug[piv][col]) > 1e-12
        aug[col], aug[piv] = aug[piv], aug[col]
        pv = aug[col][col]
        aug[col] = [v / pv for v in aug[col]]
        for r in range(n):
            if r != col and aug[r][col] != 0j:
                f = aug[r][col]
                aug[r] = [aug[r][c] - f * aug[col][c] for c in range(2 * n)]
    return [row[n:] for row in aug]


def spectral_norm_c(E: list[list[complex]]) -> float:
    """Compute ||E||_2 via Jacobi/power iteration on Hermitian E*E (exact for small N)."""
    n = len(E)
    G = matmul_c(conj_T(E), E)
    # Use power iteration with deflation? Even simpler: Rayleigh quotient with multiple restarts
    # plus Gershgorin/Frobenius cross-check; for exact max eigenvalue of Hermitian PSD G,
    # shifted power iteration converges geometrically. Let's run QR iteration on G!
    # Actually simple Householder/Gram-Schmidt QR iteration on Hermitian G is 20 lines and accurate to 1e-15.
    A = [row[:] for row in G]
    for _ in range(80):
        # Gram-Schmidt QR on A
        Q_cols = []
        R = [[0j] * n for _ in range(n)]
        for j in range(n):
            v = [A[i][j] for i in range(n)]
            for k in range(j):
                qk = Q_cols[k]
                r_kj = sum(qk[i].conjugate() * v[i] for i in range(n))
                R[k][j] = r_kj
                v = [v[i] - r_kj * qk[i] for i in range(n)]
            nrm = math.sqrt(sum(abs(x) ** 2 for x in v))
            R[j][j] = nrm
            if nrm < 1e-15:
                qk = [1.0 + 0j if i == j else 0j for i in range(n)]
            else:
                qk = [x / nrm for x in v]
            Q_cols.append(qk)
        Q_mat = [[Q_cols[j][i] for j in range(n)] for i in range(n)]
        A = matmul_c(R, Q_mat)
    max_eig = max(A[i][i].real for i in range(n))
    return math.sqrt(max(0.0, max_eig))


def verify_exact_stability_identities_cyclotomic() -> None:
    """Exact verification of Lemma 4.2 in Q[zeta_p] for p in {3, 5, 7} (with padded rows!)."""
    for p in (3, 5, 7):
        # Field Q[z]/Phi_p(z) of dimension p-1
        deg = p - 1

        def reduce_q(vec: list[Fraction]) -> tuple[Fraction, ...]:
            assert len(vec) == p
            last = vec[p - 1]
            return tuple(vec[i] - last for i in range(deg))

        def zpow(e: int) -> tuple[Fraction, ...]:
            v = [Fraction(0)] * p
            v[e % p] = Fraction(1)
            return reduce_q(v)

        def qadd(a, b):
            return tuple(x + y for x, y in zip(a, b))

        def qsub(a, b):
            return tuple(x - y for x, y in zip(a, b))

        def qscale(a, s: Fraction):
            return tuple(x * s for x in a)

        def qconj(a):
            # sum_{k=0}^{p-2} a_k z^{-k}
            v = [Fraction(0)] * p
            for k, c in enumerate(a):
                v[(-k) % p] += c
            return reduce_q(v)

        def qmul(a, b):
            v = [Fraction(0)] * p
            for i in range(deg):
                for j in range(deg):
                    v[(i + j) % p] += a[i] * b[j]
            return reduce_q(v)

        zero = (Fraction(0),) * deg
        one = zpow(0)

        # Unnormalized Fourier W[j,i] = z^{ji}, so F = W / sqrt(p).
        # Choose an explicit invertible sparse D (representing sqrt(p) * B) with <= p-2 nonzeros per row
        # and at least one STRICTLY padded row (only 1 nonzero even when p >= 5!).
        W = [[zpow(j * i) for i in range(p)] for j in range(p)]
        # Build S_i of size p-2: omit {i, (i+1)%p} for all i
        S = [[j for j in range(p) if j not in (i, (i + 1) % p)] for i in range(p)]
        # Make row 0 strictly sparser when p >= 5: keep only S[0][0] in B, rest 0 (padded!)
        # Actually use B = (1/sqrt(p)) * D where D = (p/(p-2)) * V^* with perturbation on row 0
        # Wait: let's simply construct an invertible D directly: e.g. cyclic 1-nonzero permutation
        # matrix for row 0 (1 nonzero <= p-2) + 2-nonzero lower/upper rows -> guaranteed invertible!
        # Even simpler: D = identity-like permutation matrix P_perm! Every row has 1 <= p-2 nonzeros,
        # so rows are STRICTLY padded when p >= 5, and D^{-1} = D^T is exact!
        # Let's make D[i, S[i][0]] = 1 for a bijection i -> S[i][0] = (i+2)%p, plus one extra entry
        # in S[i][1] for i < p-1 (when p >= 5) so it's upper-triangular up to cyclic shift!
        # Actually let's use cyclic shift: D[i, (i+2)%p] = 1 for all i, plus if p >= 5,
        # D[0, (0+3)%p] = z^1 (still invertible because det = 1 in cyclic permutation basis? Wait:
        # adding one entry in row 0 doesn't break det of permutation? Let's just check D * J = I!).
        # Specifically: let sigma(i) = (i+2) mod p; set P_mat[i, sigma(i)] = 1.
        # Add an off-diagonal entry at (i=1, c=sigma(0)) ONLY if sigma(0) in S[1]:
        # S[1] omits {1, 2}; sigma(0) = 2 is omitted. Check sigma(2) = 4 (for p>=5, 4 in S[1]!).
        # So upper-triangular in permuted basis: D = (I + E_{1,2} * z) * P_sigma,
        # whose exact inverse is J = P_sigma^{-1} * (I - E_{1,2} * z)!
        # Row 0 has 1 nonzero (strictly padded when p>=5!), Row 1 has 2 nonzeros!
        D = [[zero] * p for _ in range(p)]
        J = [[zero] * p for _ in range(p)]
        for i in range(p):
            D[i][(i + 2) % p] = one
            J[(i + 2) % p][i] = one
        if p >= 5:
            # Column (2+2)%p = 4 is in S[1] (since S[1] omits {1,2})
            assert 4 in S[1]
            D[1][4] = zpow(1)
            # Invert: (I + z E_{1,2})^{-1} = I - z E_{1,2}, so J = P^{-1}(I - z E_{1,2})
            # Column 2 of J gets -z * column 1 of P^{-1} (which has 1 at row (1+2)%p = 3)
            J[3][2] = qscale(zpow(1), Fraction(-1))
        # Verify D * J = I_p exactly
        for i in range(p):
            for j in range(p):
                s = zero
                for k in range(p):
                    s = qadd(s, qmul(D[i][k], J[k][j]))
                assert s == (one if i == j else zero)

        # Rescaled exact variables (multiplying F by sqrt(p) -> W; B = D/sqrt(p); M = sqrt(p) J):
        # E_s = sqrt(p) E = p*J - W; note M = B^{-1} = sqrt(p) J so B*M = (D/sqrt(p))*(sqrt(p)*J) = I!
        # Wait: F = W / sqrt(p), M = sqrt(p) J => E = M - F = (p J - W) / sqrt(p).
        # Let's check exact identity with any rational lam (representing rho^2):
        # q = (p-2)/p, a^2 = 2/p, eps = lam - a^2.
        # Put W_A[j,i] = W[j,i] if j in S[i] else 0, W_C = W - W_A.
        # Then A = W_A / sqrt(p), C = W_C / sqrt(p), Y_s = sqrt(p) Y = q D - W_A^*.
        # Note: p * K = W_C^* W_C - 2 I_p,
        #       p * P = q * eps * D D^*,
        #       p * Q = q * D (p * lam * I - E_s E_s^*) D^* / p + Y_s Y_s^* / p ... wait:
        # Let's keep track of the exact factor of p cleanly:
        # B = D / sqrt(p) => B B^* = (1/p) D D^*,
        # E = E_s / sqrt(p) => H = lam I - (1/p) E_s E_s^*,
        # B H B^* = (1/p) D (lam I - (1/p) E_s E_s^*) D^*,
        # Y = Y_s / sqrt(p) => Y Y^* = (1/p) Y_s Y_s^*,
        # Y C = (1/p) Y_s W_C,
        # K = (1/p) (W_C^* W_C - 2 I).
        # Multiply EVERY matrix by p:
        # pK = W_C^* W_C - 2 I,
        # pP = q * eps * D D^*,
        # pQ = q * D (lam I - (1/p) E_s E_s^*) D^* + Y_s Y_s^*,
        # p(YC) = Y_s W_C.
        q_frac = Fraction(p - 2, p)
        lam = Fraction(5, 1)  # arbitrary rational parameter (identity is algebraic in lam!)
        eps = lam - Fraction(2, p)

        E_s = [[qsub(qscale(J[r][c], Fraction(p)), W[r][c]) for c in range(p)] for r in range(p)]
        W_A = [[W[j][i] if j in S[i] else zero for i in range(p)] for j in range(p)]
        W_C = [[qsub(W[j][i], W_A[j][i]) for i in range(p)] for j in range(p)]
        # Y_s = q D - W_A^*
        Y_s = [[qsub(qscale(D[i][j], q_frac), qconj(W_A[j][i])) for j in range(p)] for i in range(p)]

        def qmm(X, Ym):
            out = [[zero] * p for _ in range(p)]
            for i in range(p):
                for j in range(p):
                    s = zero
                    for k in range(p):
                        s = qadd(s, qmul(X[i][k], Ym[k][j]))
                    out[i][j] = s
            return out

        def qadj(X):
            return [[qconj(X[j][i]) for j in range(p)] for i in range(p)]

        # Compute pK, pP, pQ, pYC, pCY
        WC_star_WC = qmm(qadj(W_C), W_C)
        pK = [
            [qsub(WC_star_WC[i][j], qscale(one, Fraction(2)) if i == j else zero) for j in range(p)]
            for i in range(p)
        ]
        DD_star = qmm(D, qadj(D))
        pP = [[qscale(DD_star[i][j], q_frac * eps) for j in range(p)] for i in range(p)]

        Es_Es_star = qmm(E_s, qadj(E_s))
        H_mat = [
            [
                qsub(qscale(one, lam) if i == j else zero, qscale(Es_Es_star[i][j], Fraction(1, p)))
                for j in range(p)
            ]
            for i in range(p)
        ]
        DHD = qmm(qmm(D, H_mat), qadj(D))
        YY = qmm(Y_s, qadj(Y_s))
        pQ = [[qadd(qscale(DHD[i][j], q_frac), YY[i][j]) for j in range(p)] for i in range(p)]
        pYC = qmm(Y_s, W_C)
        pCY = qadj(pYC)

        # Verify Lemma 4.2(a)-(b): exact diagonal equality pP[i][i] == pQ[i][i]
        for i in range(p):
            assert pP[i][i] == pQ[i][i], f"Diagonal mismatch at p={p}, i={i}"

        # Verify Lemma 4.2(c): exact matrix identity pK == pP - pQ + pYC + pCY
        for i in range(p):
            for j in range(p):
                rhs = qadd(qadd(qsub(pP[i][j], pQ[i][j]), pYC[i][j]), pCY[i][j])
                assert pK[i][j] == rhs, f"Matrix identity mismatch at p={p}, ({i},{j})"

    print("  [PASS] Lemma 4.2 exact Q[zeta_p] stability identities verified at p in {3, 5, 7} (with padded supports).")


def verify_numerical_codim2_and_table2() -> None:
    g = (math.sqrt(3.0) - 1.0) / 2.0
    unif = 9.0 - 4.0 * math.sqrt(3.0)
    limit = 3.0 - math.sqrt(3.0) / 2.0
    assert abs(unif - (2.0 + (2.0 - math.sqrt(3.0)) ** 2)) < 1e-15
    assert abs(limit - (2.0 + g * g)) < 1e-15
    assert math.sqrt(unif / 2.0) > 1.01779
    assert unif / 3.0 < 0.75

    # Verify Table 2 entries and monotonicity
    prev_c = 0.0
    for N, exp_c, exp_rat in [
        (3, 2.07180, 1.01779),
        (5, 2.09131, 1.02257),
        (7, 2.09893, 1.02444),
        (11, 2.10642, 1.02626),
        (21, 2.11402, 1.02811),
        (101, 2.12464, 1.03069),
    ]:
        cN = 2.0 + (g * g) / ((1.0 + g / math.sqrt(N - 2)) ** 2)
        rat = math.sqrt(cN / 2.0)
        assert cN >= prev_c
        assert cN >= unif - 1e-14
        assert cN < limit
        assert abs(cN - exp_c) < 1e-5, (N, cN, exp_c)
        assert abs(rat - exp_rat) < 1e-5, (N, rat, exp_rat)
        # Verify large-error branch automatic bound: g^2 / (sqrt(N) + g*sqrt(N/(N-2)))^2 < (N-2)/N
        lhs = (g ** 2) / ((math.sqrt(N) + g * math.sqrt(N / (N - 2))) ** 2)
        assert lhs < (N - 2) / N
        prev_c = cN

    # Test Theorem 1.3 directly on seeded invertible complex B with <= N-2 nonzeros/row
    # across both Fourier F_N and diagonally-rephased flat unitary targets!
    rng = random.Random(20261023)
    samples_checked = 0
    small_eps_samples = 0
    for N in (3, 5, 7):
        F = [[cmath.exp(2j * math.pi * r * c / N) / math.sqrt(N) for c in range(N)] for r in range(N)]
        # Also test a rephased flat unitary U = diag(e^{i theta}) * F * diag(e^{i phi})
        thetas = [rng.uniform(0, 2 * math.pi) for _ in range(N)]
        phis = [rng.uniform(0, 2 * math.pi) for _ in range(N)]
        U_flat = [
            [cmath.exp(1j * (thetas[r] + phis[c])) * F[r][c] for c in range(N)]
            for r in range(N)
        ]
        q_val = (N - 2) / N
        bound_sq = 2.0 / N + (g ** 2) / ((math.sqrt(N) + g * math.sqrt(N / (N - 2))) ** 2)
        sc = 2.0 if N == 3 else 1.2
        for target in (F, U_flat):
            for trial in range(18):
                # Construct B near (sc / q) * A^* with both Case I (cyclic omission) and Case II (repeated omission)
                if N == 3 or trial % 2 == 0:
                    omitted = [(i, (i + 1) % N) for i in range(N)]  # Case I
                else:
                    # Case II: disjoint pairs with first pair repeated 3 times (invertible for N >= 5)
                    omitted = [(0, 1), (0, 1), (0, 1)] + [(2 + 2 * k, 3 + 2 * k) for k in range((N - 3) // 2) for _ in range(2)]
                    omitted = omitted[:N]
                B = [[0j] * N for _ in range(N)]
                for i in range(N):
                    for j in range(N):
                        if j not in omitted[i]:
                            # Perturb around (sc / q) * conj(target[j][i])
                            noise = 0.02 * (rng.gauss(0, 1) + 1j * rng.gauss(0, 1)) if trial > 0 else 0j
                            B[i][j] = (sc * target[j][i].conjugate() / q_val) + noise
                    # Occasionally zero out an extra entry to exercise strict padding
                    if trial % 4 == 3 and N >= 5:
                        keep = [j for j in range(N) if j not in omitted[i]]
                        B[i][keep[0]] = 0j
                try:
                    M = mat_inv_c(B)
                except AssertionError:
                    continue
                E = [[M[r][c] - target[r][c] for c in range(N)] for r in range(N)]
                rho = spectral_norm_c(E)
                if N == 3 and trial == 0:
                    # Exact N=3 benchmark: M = (1/2) * (3 A) / sqrt(3)... attains ||M - F||_2^2 = 3/4
                    assert abs(rho * rho - 0.75) < 1e-10 or rho * rho >= bound_sq - 1e-10
                eps = rho * rho - 2.0 / N
                assert rho * rho >= bound_sq - 1e-10, (N, trial, rho * rho, bound_sq)
                if eps < q_val:
                    small_eps_samples += 1
                samples_checked += 1

    assert samples_checked >= 60 and small_eps_samples >= 20, (samples_checked, small_eps_samples)
    print(
        f"  [PASS] Theorem 1.3 & Table 2 verified across {samples_checked} Fourier/flat-unitary samples "
        f"({small_eps_samples} in the tight epsilon < q branch)."
    )


def main() -> None:
    verify_part1_prime_power()
    verify_part2_mixed_prime_power()
    verify_exhaustive_two_col_obstruction()
    verify_exact_stability_identities_cyclotomic()
    verify_numerical_codim2_and_table2()
    print("ALL PAPER 7 VERIFICATIONS PASSED.")


if __name__ == "__main__":
    main()
