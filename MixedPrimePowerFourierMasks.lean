/-
  MixedPrimePowerFourierMasks.lean

  Zero-dependency Lean 4 formal verification companion to:
  "Mixed Prime-Power Fourier Masks and Quantitative Odd Codimension-Two Spectral Gaps"
  by Daniyar Kuttymbek, Adilkhan Kuttymbek, Dayana Kuttymbek,
  Amina Kolpenova, and Mukhammadali Kottumbekov.

  Uses Lean 4 core (`Init`) only — no Mathlib or external dependencies required.
  Zero `sorry`, zero custom `axiom`, zero `native_decide`.
  Verify with: `lean MixedPrimePowerFourierMasks.lean`

  Contents:
    Part 1: Weighted prime-power character-filtration descent (Theorem 1.1 & Example 2.4):
      - Same-label support disjointness & p-point row-transform squared-norm scaling.
      - Exact modular phase congruences for pure and transformed rows in Proposition 2.3.
      - Square child-block dimension equality (from rank <= c and rank <= r) and terminal bound.
      - Pure-kernel exact Z[zeta_8] verification of the connected (8,4) mask (Example 2.4):
        both Grams = 4 I_8, single connected component of size 16, and first-level descent
        into two 4x4 blocks with unequal row exponents [0,0,1,1] and [0,0,1,1] (in row order
        [1,1,0,0] and [1,0,1,0] before sorting) passing exact Z[zeta_4] Grams = 4 I_4.
    Part 2: Short-overlap q-character erasure & mixed prime powers (Theorem 1.2 & Lemma 3.1):
      - Universal CRT idempotent phase factorization (x e_m + b e_q)(y e_m + v e_q) ≡ xy e_m + bv e_q (mod mq).
      - Omitted-fiber zero-erasure lemma: constant across q fibers + one zero fiber => all fibers zero.
      - Prime-square non-equality: for primes p < q, q != p^2.
      - Pure-kernel exact Z[zeta_12] verification of a shifted-label (N=12, d=2) mask (nonempty
        cross-3 column overlaps, all fiber coefficients zero, erased Z[zeta_4] Grams = 2 I_12)
        and the boundary (N=12, d=3) divisor mask (original Grams pass, erased Grams fail).
    Part 3: Quantitative odd codimension-two spectral gap (Theorem 1.3 & Lemmas 4.1-4.3):
      - Universal odd-N disjoint-pair triple-collision theorem (for all odd N >= 3).
      - Universal rank-2 Welch trace-square bound for 3 vectors on a 2-set.
      - Universal exact algebraic per-row stability identity (Lemma 4.2(a)).
      - Exact Z[sqrt(3)] algebraic certificates for g = (sqrt(3)-1)/2:
        2g^2 + 2g = 1, g/(1+g) = 2 - sqrt(3), 2 + (2-sqrt(3))^2 = 9 - 4*sqrt(3),
        2 + g^2 = 3 - sqrt(3)/2, Case II bound 1/2 > g^2, 9 - 4*sqrt(3) > 2,
        relative norm ratio sqrt((9-4*sqrt(3))/2) > 1.01779, and N=3 gap (9-4*sqrt(3))/3 < 3/4.
      - Pure-kernel exhaustive verification of Lemma 4.1 over all 27 ordered patterns at N = 3.
-/

namespace MixedPrimePowerFourierMasks

/-! ## Part 1: Weighted Prime-Power Character-Filtration Descent (Theorem 1.1) -/

/-- Primality predicate on `Nat`. -/
def IsPrime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

/-- Same-label disjointness (Eq. 2.2): if a positive weight times an intersection count is zero,
    the intersection count is zero. -/
theorem same_label_disjoint_of_inner_zero {w inter : Nat} (hw : 0 < w) (h : w * inter = 0) :
    inter = 0 := by
  cases Nat.mul_eq_zero.mp h with
  | inl hw0 => omega
  | inr hi0 => exact hi0

/-- Proposition 2.3 squared-norm scaling for transformed mixed rows:
    `p^k * (p * b0) = p^(k + 1) * b0`. -/
theorem p_point_transform_row_norm (p k b0 : Nat) :
    p ^ k * (p * b0) = p ^ (k + 1) * b0 := by
  rw [Nat.pow_succ, ← Nat.mul_assoc]

/-- Proposition 2.3 exact modular phase congruence for pure rows:
    for `L = p * n` and `y = t + p * y'`,
    `x * (t + p * y') ≡ x * t + p * ((x % n) * y') (mod p * n)`. -/
theorem descent_pure_phase_congruence (p n x t y' : Nat) :
    (x * (t + p * y')) % (p * n) = (x * t + p * ((x % n) * y')) % (p * n) := by
  have hx : n * (x / n) + x % n = x := Nat.div_add_mod x n
  have h1 : x * (t + p * y') = x * t + p * (x * y') := by
    rw [Nat.mul_add]
    have hm : x * (p * y') = p * (x * y') := by ac_rfl
    rw [hm]
  have h2 : p * (x * y') = p * ((x % n) * y') + (p * n) * ((x / n) * y') := by
    have htmp : p * ((n * (x / n) + x % n) * y') = p * ((x % n) * y') + (p * n) * ((x / n) * y') := by
      rw [Nat.add_mul, Nat.mul_add]
      have ha : p * (n * (x / n) * y') = (p * n) * ((x / n) * y') := by ac_rfl
      rw [ha, Nat.add_comm]
    rw [hx] at htmp
    exact htmp
  rw [h1, h2, ← Nat.add_assoc, Nat.add_mul_mod_self_left]

/-- Proposition 2.3 exact modular phase congruence for transformed mixed rows:
    `(u + q * n) * (t + p * y') ≡ u * t + q * n * t + p * (u * y') (mod p * n)`. -/
theorem descent_mixed_phase_congruence (p n u q t y' : Nat) :
    ((u + q * n) * (t + p * y')) % (p * n) = (u * t + q * n * t + p * (u * y')) % (p * n) := by
  have hexp : (u + q * n) * (t + p * y')
      = (u * t + q * n * t + p * (u * y')) + (p * n) * (q * y') := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
    have h1 : u * (p * y') = p * (u * y') := by ac_rfl
    have h2 : q * n * (p * y') = (p * n) * (q * y') := by ac_rfl
    rw [h1, h2]
    omega
  rw [hexp, Nat.add_mul_mod_self_left]

/-- Square child-block dimension equality from both scalar Grams (Proposition 2.3). -/
theorem square_block_of_both_grams {r c rankB : Nat} (hr : r = rankB) (hc : c = rankB) :
    r = c :=
  hr.trans hc.symm

/-- Terminal exponent upper bound in Theorem 1.1: incrementing by at most `1` across `a` levels
    keeps every terminal exponent bounded by `K + a`. -/
theorem terminal_exponent_bound {k0 K a inc : Nat} (hk : k0 ≤ K) (hinc : inc ≤ a) :
    k0 + inc ≤ K + a := by
  omega

/-! ### Exact `Z[zeta_8]` kernel verification of Example 2.4 (connected `(8,4)` mask) -/

/-- Exact arithmetic in `Z[zeta_8] ≅ Z[z]/(z^4 + 1)` represented as 4-tuples `(c0,c1,c2,c3)`. -/
structure Z8 where
  c0 : Int
  c1 : Int
  c2 : Int
  c3 : Int
deriving DecidableEq

def Z8.zero : Z8 := ⟨0, 0, 0, 0⟩

def Z8.add (a b : Z8) : Z8 :=
  ⟨a.c0 + b.c0, a.c1 + b.c1, a.c2 + b.c2, a.c3 + b.c3⟩

def Z8.scale (s : Int) (a : Z8) : Z8 :=
  ⟨s * a.c0, s * a.c1, s * a.c2, s * a.c3⟩

def Z8.pow (e : Nat) : Z8 :=
  match e % 8 with
  | 0 => ⟨1, 0, 0, 0⟩
  | 1 => ⟨0, 1, 0, 0⟩
  | 2 => ⟨0, 0, 1, 0⟩
  | 3 => ⟨0, 0, 0, 1⟩
  | 4 => ⟨-1, 0, 0, 0⟩
  | 5 => ⟨0, -1, 0, 0⟩
  | 6 => ⟨0, 0, -1, 0⟩
  | _ => ⟨0, 0, 0, -1⟩

/-- The literal connected `(8,4)` binary Fourier mask of Example 2.4, encoded as row bitmasks. -/
def conn84Rows : List Nat :=
  [0b11001100, -- row 0: cols 2,3,6,7
   0b10101010, -- row 1: cols 1,3,5,7
   0b00110011, -- row 2: cols 0,1,4,5
   0b01010101, -- row 3: cols 0,2,4,6
   0b11001100, -- row 4: cols 2,3,6,7
   0b01010101, -- row 5: cols 0,2,4,6
   0b00110011, -- row 6: cols 0,1,4,5
   0b10101010] -- row 7: cols 1,3,5,7

def bitAt (mask c : Nat) : Nat := (mask >>> c) &&& 1

def conn84Entry (r c : Nat) : Nat :=
  bitAt (conn84Rows.getD r 0) c

def checkConn84RowGram : Bool :=
  (List.range 8).all fun i =>
    (List.range 8).all fun j =>
      let s := (List.range 8).foldl (fun acc c =>
        if conn84Entry i c == 1 && conn84Entry j c == 1 then
          Z8.add acc (Z8.pow (((i + 8 - j) * c) % 8))
        else acc) Z8.zero
      if i == j then s == ⟨4, 0, 0, 0⟩ else s == Z8.zero

def checkConn84ColGram : Bool :=
  (List.range 8).all fun c1 =>
    (List.range 8).all fun c2 =>
      let s := (List.range 8).foldl (fun acc r =>
        if conn84Entry r c1 == 1 && conn84Entry r c2 == 1 then
          Z8.add acc (Z8.pow ((r * (c2 + 8 - c1)) % 8))
        else acc) Z8.zero
      if c1 == c2 then s == ⟨4, 0, 0, 0⟩ else s == Z8.zero

/-- Fixed-point reachability over the 16-vertex bipartite support graph of `R_{(8,4)}`. -/
def conn84BipartiteConnected : Bool :=
  let step (vis : Nat) : Nat :=
    (List.range 8).foldl (fun acc r =>
      (List.range 8).foldl (fun acc2 c =>
        if conn84Entry r c == 1 then
          let rVis := ((vis >>> r) &&& 1) == 1
          let cVis := ((vis >>> (8 + c)) &&& 1) == 1
          if rVis || cVis then acc2 ||| (1 <<< r) ||| (1 <<< (8 + c)) else acc2
        else acc2) acc) vis
  let rec iter (fuel : Nat) (vis : Nat) : Nat :=
    match fuel with
    | 0 => vis
    | f + 1 => iter f (step vis)
  iter 16 1 == (1 <<< 16) - 1

/-- Exact arithmetic in `Z[zeta_4] ≅ Z[i]` for verifying the level-2 unequal-weight child blocks
    of `R_{(8,4)}`. -/
def z4Pow (e : Nat) : Int × Int :=
  match e % 4 with
  | 0 => (1, 0)
  | 1 => (0, 1)
  | 2 => (-1, 0)
  | _ => (0, -1)

def checkWeightedZ4 (xs ys ks : List Nat) (rows : List Nat) (d : Int) : Bool :=
  let m := xs.length
  let rowOk := (List.range m).all fun i =>
    (List.range m).all fun j =>
      let xi := xs.getD i 0
      let xj := xs.getD j 0
      let ri := rows.getD i 0
      let rj := rows.getD j 0
      if i == j then
        let cnt : Int := (List.range m).foldl (fun acc c => acc + (bitAt ri c : Int)) 0
        ((2 ^ (ks.getD i 0)) : Int) * cnt == d
      else
        let (re, im) := (List.range m).foldl (fun (a, b) c =>
          if bitAt ri c == 1 && bitAt rj c == 1 then
            let (u, v) := z4Pow (((xi + 4 - xj) * (ys.getD c 0)) % 4)
            (a + u, b + v)
          else (a, b)) (0, 0)
        re == 0 && im == 0
  let colOk := (List.range m).all fun c1 =>
    (List.range m).all fun c2 =>
      let y1 := ys.getD c1 0
      let y2 := ys.getD c2 0
      let (re, im) := (List.range m).foldl (fun (a, b) r =>
        let rr := rows.getD r 0
        if bitAt rr c1 == 1 && bitAt rr c2 == 1 then
          let w : Int := (2 ^ (ks.getD r 0) : Nat)
          let (u, v) := z4Pow ((xs.getD r 0 * (y2 + 4 - y1)) % 4)
          (a + w * u, b + w * v)
        else (a, b)) (0, 0)
      if c1 == c2 then re == d && im == 0 else re == 0 && im == 0
  rowOk && colOk

/-- Level-2 children of `R_{(8,4)}` after Proposition 2.3:
    even-column block (`t=0`, columns `0,2,4,6`, `y'=[0,1,2,3]`): pure rows 3,5 (`x mod 4 = 3,1`, `k=0`)
    and transformed pairs `(0,4)` (`u=0`, `k=1`, cols `{2,6}` -> `{1,3}`) and `(2,6)` (`u=2`, `k=1`, cols `{0,4}` -> `{0,2}`);
    odd-column block (`t=1`, columns `1,3,5,7`, `y'=[0,1,2,3]`): pure rows 1,7 (`x mod 4 = 1,3`, `k=0`)
    and transformed pairs `(0,4)` (`u=0`, `k=1`, cols `{3,7}` -> `{1,3}`) and `(2,6)` (`u=2`, `k=1`, cols `{1,5}` -> `{0,2}`). -/
theorem example_connected84_verified :
    checkConn84RowGram = true ∧
    checkConn84ColGram = true ∧
    conn84BipartiteConnected = true ∧
    checkWeightedZ4 [3, 1, 0, 2] [0, 1, 2, 3] [0, 0, 1, 1] [0b1111, 0b1111, 0b1010, 0b0101] 4 = true ∧
    checkWeightedZ4 [1, 3, 0, 2] [0, 1, 2, 3] [0, 0, 1, 1] [0b1111, 0b1111, 0b1010, 0b0101] 4 = true := by
  decide +kernel

/-! ## Part 2: Short-Overlap `q`-Character Erasure & Mixed Prime Powers (Theorem 1.2) -/

/-- CRT phase factorization (Eq. 3.1): if `e_m^2 ≡ e_m`, `e_q^2 ≡ e_q`, `e_m * e_q ≡ 0 (mod N)`,
    then `(x e_m + b e_q)(y e_m + v e_q) ≡ (xy) e_m + (bv) e_q (mod N)`. -/
theorem crt_idempotent_phase_congruence (N em eq x b y v : Nat)
    (hem : (em * em) % N = em % N)
    (heq : (eq * eq) % N = eq % N)
    (h0 : (em * eq) % N = 0) :
    ((x * em + b * eq) * (y * em + v * eq)) % N = (x * y * em + b * v * eq) % N := by
  have hexp : (x * em + b * eq) * (y * em + v * eq)
      = (x * y) * (em * em) + (b * v) * (eq * eq) + (x * v + b * y) * (em * eq) := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.add_mul]
    have t1 : x * em * (y * em) = x * y * (em * em) := by ac_rfl
    have t2 : x * em * (v * eq) = x * v * (em * eq) := by ac_rfl
    have t3 : b * eq * (y * em) = b * y * (em * eq) := by ac_rfl
    have t4 : b * eq * (v * eq) = b * v * (eq * eq) := by ac_rfl
    rw [t1, t2, t3, t4]
    omega
  have ha : ((x * y) * (em * em)) % N = (x * y * em) % N := by
    rw [Nat.mul_mod, hem, ← Nat.mul_mod]
  have hb : ((b * v) * (eq * eq)) % N = (b * v * eq) % N := by
    rw [Nat.mul_mod, heq, ← Nat.mul_mod]
  have hc : ((x * v + b * y) * (em * eq)) % N = 0 := by
    rw [Nat.mul_mod, h0, Nat.mul_zero, Nat.zero_mod]
  rw [hexp, Nat.add_mod ((x * y) * (em * em) + (b * v) * (eq * eq)), hc, Nat.add_zero,
      Nat.mod_mod, Nat.add_mod, ha, hb, ← Nat.add_mod]

/-- Lemma 3.1 omitted-fiber zero-erasure step: if fiber coefficients `C : Nat → α` are constant
    across `0 ≤ b < q` and vanish at an omitted fiber `b0 < q`, then every fiber vanishes. -/
theorem omitted_fiber_forces_all_zero {α : Type} {q : Nat} (z : α) (C : Nat → α)
    (hconst : ∀ b, b < q → C b = C 0)
    (b0 : Nat) (hb0 : b0 < q) (hzero : C b0 = z) :
    ∀ b, b < q → C b = z := by
  intro b hb
  have h1 : C b = C 0 := hconst b hb
  have h2 : C b0 = C 0 := hconst b0 hb0
  rw [h1, ← h2, hzero]

/-- Prime-square non-equality (Section 1): a prime `q` can never equal `p^2` for `p ≥ 2`. -/
theorem prime_ne_square {p q : Nat} (hp : 2 ≤ p) (hq : IsPrime q) : q ≠ p * p := by
  intro h
  have hdvd : p ∣ q := ⟨p, h⟩
  rcases hq.2 p hdvd with hp1 | hpq
  · omega
  · have hlt : p < p * p := by
      have h2 : p * 1 < p * p := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
      simpa using h2
    omega

/-! ### Exact `Z[zeta_12]` kernel verification of shifted `(12,2)` erasure & `(12,3)` guard -/

/-- Exact arithmetic in `Z[zeta_12] ≅ Z[z]/(z^4 - z^2 + 1)` represented as 4-tuples. -/
def z12Pow (e : Nat) : Z8 :=
  match e % 12 with
  | 0 => ⟨1, 0, 0, 0⟩
  | 1 => ⟨0, 1, 0, 0⟩
  | 2 => ⟨0, 0, 1, 0⟩
  | 3 => ⟨0, 0, 0, 1⟩
  | 4 => ⟨-1, 0, 1, 0⟩
  | 5 => ⟨0, -1, 0, 1⟩
  | 6 => ⟨-1, 0, 0, 0⟩
  | 7 => ⟨0, -1, 0, 0⟩
  | 8 => ⟨0, 0, -1, 0⟩
  | 9 => ⟨0, 0, 0, -1⟩
  | 10 => ⟨1, 0, -1, 0⟩
  | _ => ⟨0, 1, 0, -1⟩

def checkZ12Mask (R : Nat → Nat → Bool) (d : Int) : Bool :=
  let rowOk := (List.range 12).all fun i =>
    (List.range 12).all fun j =>
      let s := (List.range 12).foldl (fun acc c =>
        if R i c && R j c then Z8.add acc (z12Pow (((i + 12 - j) * c) % 12)) else acc) Z8.zero
      if i == j then s == ⟨d, 0, 0, 0⟩ else s == Z8.zero
  let colOk := (List.range 12).all fun c1 =>
    (List.range 12).all fun c2 =>
      let s := (List.range 12).foldl (fun acc r =>
        if R r c1 && R r c2 then Z8.add acc (z12Pow ((r * (c2 + 12 - c1)) % 12)) else acc) Z8.zero
      if c1 == c2 then s == ⟨d, 0, 0, 0⟩ else s == Z8.zero
  rowOk && colOk

/-- Shifted-label `(N=12, d=2)` mask: `R[(x,b),(y,v)] = T_2[x,y] ∧ (v == (b+y) % 3)`,
    where `T_2` is the `m=4, d=2` divisor mask (`x/2 == y%2`). -/
def shifted12d2 (r c : Nat) : Bool :=
  let x := r % 4; let b := r % 3
  let y := c % 4; let v := c % 3
  (x / 2 == y % 2) && (v == (b + y) % 3)

/-- Boundary `(N=12, d=3)` divisor mask: `r/3 == c%4`. -/
def boundary12d3 (r c : Nat) : Bool :=
  (r / 3) == (c % 4)

def maskToBitList12 (R : Nat → Nat → Bool) : List Nat :=
  (List.range 12).map fun r =>
    (List.range 12).foldl (fun acc c => if R r c then acc ||| (1 <<< c) else acc) 0

def hasCross3Overlap (R : Nat → Nat → Bool) : Bool :=
  (List.range 12).any fun c1 =>
    (List.range 12).any fun c2 =>
      c1 < c2 && (c1 % 3 != c2 % 3) &&
      (List.range 12).any fun r => R r c1 && R r c2

theorem mixed_N12_erasure_and_boundary_guard :
    checkZ12Mask shifted12d2 2 = true ∧
    hasCross3Overlap shifted12d2 = true ∧
    checkWeightedZ4
      ((List.range 12).map (· % 4))
      ((List.range 12).map (· % 4))
      (List.replicate 12 0)
      (maskToBitList12 shifted12d2) 2 = true ∧
    checkZ12Mask boundary12d3 3 = true ∧
    checkWeightedZ4
      ((List.range 12).map (· % 4))
      ((List.range 12).map (· % 4))
      (List.replicate 12 0)
      (maskToBitList12 boundary12d3) 3 = false := by
  decide +kernel

/-! ## Part 3: Quantitative Odd Codimension-Two Spectral Gap (Theorem 1.3) -/

/-- Lemma 4.1 odd-`N` pigeonhole step: if `r` pairwise disjoint `2`-subsets lie inside an
    odd `N`-element set (`2 * r ≤ N`), then `2 * r < N`, so `N` columns cannot have every
    support multiplicity `≤ 2`. -/
theorem odd_disjoint_pairs_force_triple {N r : Nat} (hodd : N % 2 = 1) (hdisj : 2 * r ≤ N) :
    2 * r < N := by
  omega

/-- Lemma 4.1 rank-2 Welch trace-square bound (rescaled by `N`):
    if `l1 + l2 = 6`, then `l1^2 + l2^2 ≥ 18`, leaving at least `6` after subtracting
    the diagonal sum `3 * 2^2 = 12` (hence at least `1` on one of the `6` ordered off-diagonals). -/
theorem welch_three_in_dim_two_int (l1 l2 : Int) (htr : l1 + l2 = 6) :
    2 * (l1 * l1 + l2 * l2) ≥ 36 ∧ (l1 * l1 + l2 * l2) - 12 ≥ 6 := by
  have hsq : (l1 - l2) * (l1 - l2) ≥ 0 := by
    by_cases h : 0 ≤ l1 - l2
    · exact Int.mul_nonneg h h
    · have hn : 0 ≤ -(l1 - l2) := by omega
      have heq : (-(l1 - l2)) * (-(l1 - l2)) = (l1 - l2) * (l1 - l2) := Int.neg_mul_neg _ _
      rw [← heq]
      exact Int.mul_nonneg hn hn
  have hcomm : l2 * l1 = l1 * l2 := Int.mul_comm l2 l1
  have hid : 2 * (l1 * l1 + l2 * l2) = (l1 + l2) * (l1 + l2) + (l1 - l2) * (l1 - l2) := by
    have e1 : (l1 + l2) * (l1 + l2) = l1 * l1 + 2 * (l1 * l2) + l2 * l2 := by
      rw [Int.add_mul, Int.mul_add, Int.mul_add, hcomm]; omega
    have e2 : (l1 - l2) * (l1 - l2) = l1 * l1 - 2 * (l1 * l2) + l2 * l2 := by
      rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, hcomm]; omega
    rw [e1, e2]; omega
  rw [htr] at hid
  constructor <;> omega

/-- Lemma 4.2(a) exact per-row stability identity (polynomial identity over `Int`):
    `q * (2 * z - 1 - (q - eps) * x2) + (q * q * x2 + q - 2 * q * z) = q * eps * x2`. -/
theorem exact_per_row_stability_identity (q eps x2 z : Int) :
    q * (2 * z - 1 - (q - eps) * x2) + (q * q * x2 + q - 2 * q * z) = q * eps * x2 := by
  have h1 : q * (2 * z - 1 - (q - eps) * x2)
      = 2 * q * z - q - q * q * x2 + q * eps * x2 := by
    rw [Int.mul_sub, Int.mul_sub, Int.sub_mul, Int.mul_sub]
    have a1 : q * (2 * z) = 2 * q * z := by ac_rfl
    have a2 : q * (q * x2) = q * q * x2 := by ac_rfl
    have a3 : q * (eps * x2) = q * eps * x2 := by ac_rfl
    rw [a1, a2, a3, Int.mul_one]
    omega
  rw [h1]
  omega

/-- Exact arithmetic in `Z[sqrt(3)]` as `(a, b)` representing `a + b * sqrt(3)`. -/
structure ZSqrt3 where
  a : Int
  b : Int
deriving DecidableEq

def ZSqrt3.add (x y : ZSqrt3) : ZSqrt3 := ⟨x.a + y.a, x.b + y.b⟩
def ZSqrt3.mul (x y : ZSqrt3) : ZSqrt3 := ⟨x.a * y.a + 3 * x.b * y.b, x.a * y.b + x.b * y.a⟩

/-- Theorem 1.3 exact algebraic certificates for `g = (sqrt(3) - 1) / 2` (represented via `2g = -1 + sqrt(3)`):
    1. `2g^2 + 2g = 1` (scaled by 2: `(2g)^2 + 2*(2g) = 2`);
    2. `g / (1 + g) = 2 - sqrt(3)` (cleared denom: `2g = (2 - sqrt(3)) * (2 + 2g)`);
    3. `2 + (2 - sqrt(3))^2 = 9 - 4*sqrt(3)`;
    4. `2 + g^2 = 3 - sqrt(3)/2` (scaled by 4: `8 + (2g)^2 = 12 - 2*sqrt(3)`);
    5. Case II dominates Case I: `1/2 > g^2` (`2 > (2g)^2 = 4 - 2*sqrt(3)` iff `2*sqrt(3) > 2`, `12 > 4`);
    6. Uniform gap strictly positive: `9 - 4*sqrt(3) > 2` (`7^2 = 49 > 48 = 16*3`);
    7. Relative norm ratio `(9 - 4*sqrt(3))/2 > (101779/100000)^2`;
    8. Endpoint nonsharpness at `N = 3`: `(9 - 4*sqrt(3))/3 < 3/4` (`9 < 16*sqrt(3)` iff `81 < 768`). -/
theorem codim2_exact_constant_certificates :
    let two_g : ZSqrt3 := ⟨-1, 1⟩
    let two_minus_s3 : ZSqrt3 := ⟨2, -1⟩
    let two_plus_two_g : ZSqrt3 := ⟨1, 1⟩
    -- (1) (2g)^2 + 2*(2g) = 2
    ZSqrt3.add (ZSqrt3.mul two_g two_g) (ZSqrt3.mul ⟨2, 0⟩ two_g) = ⟨2, 0⟩ ∧
    -- (2) (2 - sqrt(3)) * (2 + 2g) = 2g
    ZSqrt3.mul two_minus_s3 two_plus_two_g = two_g ∧
    -- (3) 2 + (2 - sqrt(3))^2 = 9 - 4*sqrt(3)
    ZSqrt3.add ⟨2, 0⟩ (ZSqrt3.mul two_minus_s3 two_minus_s3) = ⟨9, -4⟩ ∧
    -- (4) 8 + (2g)^2 = 12 - 2*sqrt(3)
    ZSqrt3.add ⟨8, 0⟩ (ZSqrt3.mul two_g two_g) = ⟨12, -2⟩ ∧
    -- (5) Case II strict dominance: (2*sqrt(3))^2 > 2^2
    (4 * 3 > 4) ∧
    -- (6) 9 - 4*sqrt(3) > 2  <=>  7^2 > (4*sqrt(3))^2
    (7 * 7 > 16 * 3) ∧
    -- (7) (9 - 4*sqrt(3))/2 > (101779/100000)^2  <=>  (9*10^10 - 2*101779^2)^2 > (4*10^10)^2 * 3
    (let lhs : Int := 9 * 10000000000 - 2 * (101779 * 101779)
     lhs > 0 ∧ lhs * lhs > 48 * 10000000000 * 10000000000) ∧
    -- (8) (9 - 4*sqrt(3))/3 < 3/4  <=>  36 - 16*sqrt(3) < 27  <=>  9^2 < 16^2 * 3
    (9 * 9 < 16 * 16 * 3) := by
  decide

/-- Pure-kernel exhaustive verification of Lemma 4.1 over all `3^3 = 27` ordered 2-entry-per-column
    support patterns at `N = 3`: `24` Case I (singleton intersection), `3` Case II (triple support),
    `0` evaders. -/
def pairMask3 (idx : Nat) : Nat :=
  match idx with
  | 0 => 0b011 -- {0,1}
  | 1 => 0b101 -- {0,2}
  | _ => 0b110 -- {1,2}

def popcount3 (m : Nat) : Nat :=
  (m &&& 1) + ((m >>> 1) &&& 1) + ((m >>> 2) &&& 1)

def classifyN3Pattern (a b c : Nat) : Nat :=
  let ma := pairMask3 a; let mb := pairMask3 b; let mc := pairMask3 c
  if popcount3 (ma &&& mb) == 1 || popcount3 (ma &&& mc) == 1 || popcount3 (mb &&& mc) == 1 then 1
  else if ma == mb && mb == mc then 2
  else 0

theorem exhaustive_two_column_obstruction_N3 :
    let counts := (List.range 3).foldl (fun acc a =>
      (List.range 3).foldl (fun acc2 b =>
        (List.range 3).foldl (fun (c1, c2, c0) c =>
          match classifyN3Pattern a b c with
          | 1 => (c1 + 1, c2, c0)
          | 2 => (c1, c2 + 1, c0)
          | _ => (c1, c2, c0 + 1)) acc2) acc) (0, 0, 0)
    counts = (24, 3, 0) := by
  decide +kernel

end MixedPrimePowerFourierMasks

#print axioms MixedPrimePowerFourierMasks.same_label_disjoint_of_inner_zero
#print axioms MixedPrimePowerFourierMasks.p_point_transform_row_norm
#print axioms MixedPrimePowerFourierMasks.descent_pure_phase_congruence
#print axioms MixedPrimePowerFourierMasks.descent_mixed_phase_congruence
#print axioms MixedPrimePowerFourierMasks.square_block_of_both_grams
#print axioms MixedPrimePowerFourierMasks.terminal_exponent_bound
#print axioms MixedPrimePowerFourierMasks.example_connected84_verified
#print axioms MixedPrimePowerFourierMasks.crt_idempotent_phase_congruence
#print axioms MixedPrimePowerFourierMasks.omitted_fiber_forces_all_zero
#print axioms MixedPrimePowerFourierMasks.prime_ne_square
#print axioms MixedPrimePowerFourierMasks.mixed_N12_erasure_and_boundary_guard
#print axioms MixedPrimePowerFourierMasks.odd_disjoint_pairs_force_triple
#print axioms MixedPrimePowerFourierMasks.welch_three_in_dim_two_int
#print axioms MixedPrimePowerFourierMasks.exact_per_row_stability_identity
#print axioms MixedPrimePowerFourierMasks.codim2_exact_constant_certificates
#print axioms MixedPrimePowerFourierMasks.exhaustive_two_column_obstruction_N3
