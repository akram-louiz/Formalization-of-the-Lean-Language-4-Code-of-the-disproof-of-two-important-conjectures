import Mathlib

/-!
# Self-contained Lean 4 formalization of A. Louiz, “A disproof of the Twin Primes
# conjecture proving also that there are no Siegel Zeros”

This file is readable and checkable without the PDF.

## Setting
A chain of positive naturals `j₁, j₂, …` with `j_(i+1) = j_i + k_i` (`k_i ≥ 1`), indices
starting at 1.  A twin pair `(p-2, p)` with `p = 6 j₁ + 1` starts it; the article assumes the
numbers `p + 6∑k_i`, `p - 2 + 6∑k_i` stay twin primes, i.e. `(6 j_i - 1, 6 j_i + 1)` are twin
primes, and that this single chain gathers all twin primes above 3.

## Content (all proved unless marked *claim*)
* Part 1  – chain identities, article equations (1)–(24).
* Part 2  – averaged bounds and shifted chain, equations (28)–(47); `AlwaysM3 → j_(z+1) < 2 j_z`.
* Part 3  – remark on three consecutive odd primes, (25)–(27); iterates (48); (51), (52);
            algebra of (53).
* Part 4  – the logical skeleton: `article_core`, `article_full`.
* *Claims* kept as explicit `Prop`s/hypotheses (not asserted): `ArticleStepA` (finite `x` with
  `j_x` beyond every bound), `Claim50` (from Brun's bound (49) and the gathering assumption),
  `IndexInductionClaim`, `ChainGathersAllTwins`, `BrunUpperBound`, `HardyLittlewoodTwinPrime`,
  Heath-Brown's dichotomy `HeathBrownStatement`.

`article_core` proves: chain recurrence + `ArticleStepA` + `Claim50` ⟹ finitely many twin
primes.  `chain_set_infinite` / `article_chain_claim_inconsistent` show the article's sentence
"the set of chain numbers is not infinite" contradicts `k_i ≥ 1`.
Whether the article's inputs are true is not decided here.
-/

namespace LouizTwinPrimeArticle

open Finset

/-! ## Basic notation -/

/-- `TwinPair p` : `p` and `p + 2` are both prime. -/
def TwinPair (p : ℕ) : Prop := Nat.Prime p ∧ Nat.Prime (p + 2)

/-- Partial sum `k_1 + ... + k_m`. -/
def S (k : ℕ → ℕ) (m : ℕ) : ℕ := ∑ L ∈ Icc 1 m, k L

/-- The weighted sum `∑_{i=1}^{n} (n+1-i) * k_i`  (the article's `∑_{i=1}^{N-1} (N-i) k_i`
with `N = n + 1`). -/
def W (k : ℕ → ℕ) (n : ℕ) : ℕ := ∑ i ∈ Icc 1 n, (n + 1 - i) * k i

/-- The article's recurrence `j_(i+1) = j_i + k_i`, for every strictly positive `i`. -/
def ChainRecurrence (j k : ℕ → ℕ) : Prop :=
  ∀ i, 1 ≤ i → j (i + 1) = j i + k i

/-- The chain of the article: `j_i`, `k_i` strictly positive naturals (indices `≥ 1`)
with `j_(i+1) = j_i + k_i`. -/
structure Chain (j k : ℕ → ℕ) : Prop where
  j_pos : ∀ i, 1 ≤ i → 0 < j i
  k_pos : ∀ i, 1 ≤ i → 0 < k i
  step : ChainRecurrence j k

/-! ## Elementary lemmas on finite sums -/

lemma S_succ (k : ℕ → ℕ) (m : ℕ) : S k (m + 1) = S k m + k (m + 1) := by
  unfold S
  rw [Finset.sum_Icc_succ_top (by omega)]

lemma S_zero (k : ℕ → ℕ) : S k 0 = 0 := by simp [S]

lemma W_zero (k : ℕ → ℕ) : W k 0 = 0 := by simp [W]

lemma W_succ (k : ℕ → ℕ) (n : ℕ) : W k (n + 1) = W k n + S k (n + 1) := by
  unfold W
  rw [Finset.sum_Icc_succ_top (by omega)]
  have h : ∑ i ∈ Icc 1 n, (n + 1 + 1 - i) * k i
      = ∑ i ∈ Icc 1 n, ((n + 1 - i) * k i + k i) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_Icc.mp hi
    have : n + 1 + 1 - i = (n + 1 - i) + 1 := by omega
    rw [this]; ring
  rw [h, Finset.sum_add_distrib]
  have h2 : (n + 1 + 1 - (n + 1)) * k (n + 1) = k (n + 1) := by simp
  rw [h2]
  have h3 : S k (n + 1) = ∑ i ∈ Icc 1 n, k i + k (n + 1) := by
    unfold S; rw [Finset.sum_Icc_succ_top (by omega)]
  rw [h3]; ring

/-- `∑_{m=1}^{n} S_m = ∑_{i=1}^{n} (n+1-i) k_i`. -/
lemma sum_S_eq_W (k : ℕ → ℕ) (n : ℕ) : ∑ m ∈ Icc 1 n, S k m = W k n := by
  induction n with
  | zero => simp [W]
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih, W_succ]

/-- Shifting an index range by one. -/
lemma sum_Icc_shift {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ i ∈ Icc 1 n, f (i + 1) = ∑ i ∈ Icc 2 (n + 1), f i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih,
        Finset.sum_Icc_succ_top (show 2 ≤ n + 1 + 1 by omega)]

/-- `∑_{i=1}^{n+1} f i = f 1 + ∑_{i=2}^{n+1} f i`. -/
lemma sum_Icc_one_split {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ i ∈ Icc 1 (n + 1), f i = f 1 + ∑ i ∈ Icc 2 (n + 1), f i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih,
        Finset.sum_Icc_succ_top (show 2 ≤ n + 1 + 1 by omega)]
      rw [add_assoc]

/-- `∑_{i=2}^{M} f i = f 2 + ∑_{i=3}^{M} f i` for `2 ≤ M`. -/
lemma sum_Icc_two_split {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ i ∈ Icc 2 (n + 2), f i = f 2 + ∑ i ∈ Icc 3 (n + 2), f i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (show 2 ≤ n + 2 + 1 by omega), ih,
        Finset.sum_Icc_succ_top (show 3 ≤ n + 2 + 1 by omega)]
      rw [add_assoc]

/-! ## Equation (19): `∑_{L=1}^{i} k_L = j_(i+1) - j_1` -/

theorem chain_eq {j k : ℕ → ℕ} (h : ChainRecurrence j k) (m : ℕ) :
    j (m + 1) = j 1 + S k m := by
  induction m with
  | zero => simp [S]
  | succ m ih =>
      rw [h (m + 1) (by omega), ih, S_succ]
      ring

/-- Article equation (19), with natural-number subtraction. -/
theorem eq19 {j k : ℕ → ℕ} (h : ChainRecurrence j k) (i : ℕ) :
    ∑ L ∈ Icc 1 i, k L = j (i + 1) - j 1 := by
  have := chain_eq h i
  unfold S at this
  omega

theorem chain_mono {j k : ℕ → ℕ} (h : ChainRecurrence j k) {a b : ℕ} (ha : 1 ≤ a)
    (hab : a ≤ b) : j a ≤ j b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_refl _
  | succ b hab ih =>
      have := h b (le_trans ha hab)
      omega

theorem chain_ge_index {j k : ℕ → ℕ} (h : Chain j k) {n : ℕ} (hn : 1 ≤ n) : n ≤ j n := by
  induction n, hn using Nat.le_induction with
  | base => exact h.j_pos 1 le_rfl
  | succ n hn ih =>
      have := h.step n hn
      have := h.k_pos n hn
      omega

theorem chain_strictMono {j k : ℕ → ℕ} (h : Chain j k) {a b : ℕ} (ha : 1 ≤ a)
    (hab : a < b) : j a < j b := by
  obtain ⟨d, rfl⟩ : ∃ d, b = a + d + 1 := ⟨b - a - 1, by omega⟩
  induction d with
  | zero =>
      have h1 := h.step a ha
      have h2 := h.k_pos a ha
      simp only [Nat.add_zero]
      omega
  | succ d ih =>
      have ih' := ih (by omega)
      have h1 := h.step (a + d + 1) (by omega)
      have h2 := h.k_pos (a + d + 1) (by omega)
      have e : a + (d + 1) + 1 = a + d + 1 + 1 := by omega
      rw [e]
      omega

/-! ## Equations (23), (24) and (18) -/

/-- Equation (24) (with `N = n + 1`). -/
theorem eq24_aux {j k : ℕ → ℕ} (h : ChainRecurrence j k) (n : ℕ) :
    ∑ i ∈ Icc 1 (n + 1), j i = (n + 1) * j 1 + W k n := by
  induction n with
  | zero => simp [W]
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih, chain_eq h (n + 1), W_succ]
      ring

/-- Equation (24): `∑_{i=1}^N j_i = N j_1 + ∑_{i=1}^{N-1} (N-i) k_i`. -/
theorem eq24 {j k : ℕ → ℕ} (h : ChainRecurrence j k) {N : ℕ} (hN : 1 ≤ N) :
    ∑ i ∈ Icc 1 N, j i = N * j 1 + ∑ i ∈ Icc 1 (N - 1), (N - i) * k i := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have := eq24_aux h n
  simpa [W] using this

/-- Equation (23): `∑_{i=2}^N j_i = (N-1) j_1 + ∑_{i=1}^{N-1} (N-i) k_i`. -/
theorem eq23 {j k : ℕ → ℕ} (h : ChainRecurrence j k) {N : ℕ} (hN : 1 ≤ N) :
    ∑ i ∈ Icc 2 N, j i = (N - 1) * j 1 + ∑ i ∈ Icc 1 (N - 1), (N - i) * k i := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have h1 := eq24_aux h n
  have h2 := sum_Icc_one_split j n
  simp only [Nat.add_sub_cancel]
  unfold W at h1
  rw [h2] at h1
  have : (n + 1) * j 1 = j 1 + n * j 1 := by ring
  omega

/-- Equation (18) (with `N = n + 1`). -/
theorem eq18_aux {j k : ℕ → ℕ} (h : ChainRecurrence j k) (n : ℕ) :
    ∑ i ∈ Icc 2 (n + 1), (j i) ^ 2
      = n * (j 1) ^ 2 + 2 * j 1 * W k n + ∑ i ∈ Icc 1 n, (S k i) ^ 2 := by
  induction n with
  | zero => simp [W]
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (show 2 ≤ n + 1 + 1 by omega), ih,
        Finset.sum_Icc_succ_top (show 1 ≤ n + 1 by omega), chain_eq h (n + 1), W_succ]
      ring

/-- Equation (18). -/
theorem eq18 {j k : ℕ → ℕ} (h : ChainRecurrence j k) {N : ℕ} (hN : 1 ≤ N) :
    ∑ i ∈ Icc 2 N, (j i) ^ 2
      = (N - 1) * (j 1) ^ 2 + 2 * j 1 * (∑ i ∈ Icc 1 (N - 1), (N - i) * k i)
        + ∑ i ∈ Icc 1 (N - 1), (∑ L ∈ Icc 1 i, k L) ^ 2 := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have := eq18_aux h n
  simpa [W, S] using this

/-! ## Equations (20), (21), (22) -/

/-- Equation (20). -/
theorem eq20 {j k : ℕ → ℕ} (h : ChainRecurrence j k) {N : ℕ} (hN : 1 ≤ N) :
    ∑ i ∈ Icc 1 (N - 1), (∑ L ∈ Icc 1 i, k L) ^ 2
      = ∑ i ∈ Icc 1 (N - 1), (j (i + 1) - j 1) ^ 2
      ∧ ∑ i ∈ Icc 1 (N - 1), (j (i + 1) - j 1) ^ 2
      = ∑ i ∈ Icc 2 N, (j i - j 1) ^ 2 := by
  constructor
  · apply Finset.sum_congr rfl
    intro i _
    rw [eq19 h i]
  · obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    simpa using sum_Icc_shift (fun i => (j i - j 1) ^ 2) n

/-- Equation (21), in `ℤ` (the article's subtractions are then genuine). -/
theorem eq21 {j k : ℕ → ℕ} (h : ChainRecurrence j k) {N : ℕ} (hN : 1 ≤ N) :
    (∑ i ∈ Icc 2 N, ((j i : ℕ) : ℤ) ^ 2)
        - ∑ i ∈ Icc 1 (N - 1), (((∑ L ∈ Icc 1 i, k L : ℕ)) : ℤ) ^ 2
      = ∑ i ∈ Icc 2 N, (((j i : ℕ) : ℤ) ^ 2 - (((j i : ℕ) : ℤ) - j 1) ^ 2)
      ∧ ∑ i ∈ Icc 2 N, (((j i : ℕ) : ℤ) ^ 2 - (((j i : ℕ) : ℤ) - j 1) ^ 2)
      = ∑ i ∈ Icc 2 N, (2 * (j 1 : ℤ) * j i - (j 1 : ℤ) ^ 2)
      ∧ ∑ i ∈ Icc 2 N, (2 * (j 1 : ℤ) * j i - (j 1 : ℤ) ^ 2)
      = 2 * (j 1 : ℤ) * ∑ i ∈ Icc 2 N, (j i : ℤ) - ∑ i ∈ Icc 2 N, (j 1 : ℤ) ^ 2 := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    have hs : ∑ i ∈ Icc 1 (n + 1 - 1), (((∑ L ∈ Icc 1 i, k L : ℕ)) : ℤ) ^ 2
        = ∑ i ∈ Icc 2 (n + 1), (((j i : ℕ) : ℤ) - j 1) ^ 2 := by
      have e1 : ∑ i ∈ Icc 1 (n + 1 - 1), (((∑ L ∈ Icc 1 i, k L : ℕ)) : ℤ) ^ 2
          = ∑ i ∈ Icc 1 n, (((j (i + 1) : ℕ) : ℤ) - j 1) ^ 2 := by
        simp only [Nat.add_sub_cancel]
        apply Finset.sum_congr rfl
        intro i _
        have := chain_eq h i
        unfold S at this
        rw [this]; push_cast; ring
      rw [e1]
      exact sum_Icc_shift (fun i => (((j i : ℕ) : ℤ) - j 1) ^ 2) n
    rw [hs, ← Finset.sum_sub_distrib]
  · apply Finset.sum_congr rfl
    intro i _; ring
  · rw [Finset.mul_sum, ← Finset.sum_sub_distrib]

/-- Equation (22), in `ℤ`. -/
theorem eq22 {j k : ℕ → ℕ} (h : ChainRecurrence j k) {N : ℕ} (hN : 1 ≤ N) :
    (∑ i ∈ Icc 2 N, ((j i : ℕ) : ℤ) ^ 2)
        - ∑ i ∈ Icc 1 (N - 1), (((∑ L ∈ Icc 1 i, k L : ℕ)) : ℤ) ^ 2
      = 2 * (j 1 : ℤ) * ∑ i ∈ Icc 2 N, (j i : ℤ) - ((N : ℤ) - 1) * (j 1 : ℤ) ^ 2 := by
  obtain ⟨h1, h2, h3⟩ := eq21 h hN
  rw [h1, h2, h3]
  simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  congr 2
  have : N + 1 - 2 = N - 1 := by omega
  rw [this]
  push_cast [Nat.cast_sub hN]
  ring

/-- The derivation of (23) from (18) and (22), as in the article:
`2 j_1 (∑ j_i) - (N-1) j_1² = (N-1) j_1² + 2 j_1 T`, then divide by `2 j_1 > 0`. -/
theorem eq23_of_eq18_eq22 {j k : ℕ → ℕ} (h : ChainRecurrence j k) (hj1 : 0 < j 1)
    {N : ℕ} (hN : 1 ≤ N) :
    ∑ i ∈ Icc 2 N, j i = (N - 1) * j 1 + ∑ i ∈ Icc 1 (N - 1), (N - i) * k i := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have h18 := eq18 h hN
  have h22 := eq22 h hN
  simp only [Nat.add_sub_cancel] at h18 h22 ⊢
  have h18z := congrArg (fun x : ℕ => (x : ℤ)) h18
  push_cast at h18z h22
  have hpos : (0 : ℤ) < 2 * (j 1 : ℤ) := by positivity
  have key : 2 * (j 1 : ℤ) * (∑ i ∈ Icc 2 (n + 1), (j i : ℤ))
      = 2 * (j 1 : ℤ) * ((n : ℤ) * j 1
        + ∑ i ∈ Icc 1 n, ((n + 1 - i : ℕ) : ℤ) * (k i : ℤ)) := by
    linarith
  have hz := mul_left_cancel₀ hpos.ne' key
  exact_mod_cast hz

/-! ## Equations (1)–(17) -/

/-- Hypotheses (1)–(4), (6) of the article.  `Y` is an integer (it is `X - (p - 2)`),
and (6) is recorded as `p = 6 j_1 + 1`, i.e. `p - 2 = 6 j_1 - 1`. -/
structure Setup (X p : ℕ) (Y : ℤ) (j1 : ℕ) : Prop where
  hX : 5 < X                              -- (1)
  hp : Nat.Prime p ∧ 5 < p                -- (2)
  htwin : Nat.Prime (p - 2)               -- (3) `p - 2` and `p` are twin primes
  hXY : (X : ℤ) = ((p : ℤ) - 2) + Y       -- (4)
  hj1 : 1 ≤ j1
  hp6 : p = 6 * j1 + 1                    -- (6)

/-- Equation (5). -/
theorem eq5 {X p : ℕ} {Y : ℤ} (hXY : (X : ℤ) = ((p : ℤ) - 2) + Y) :
    (X : ℤ) * p = ((p : ℤ) - 2) * p + Y * p := by
  rw [hXY]; ring

/-- Equation (6), in `ℕ`. -/
theorem eq6 {p j1 : ℕ} (hj1 : 1 ≤ j1) (hp6 : p = 6 * j1 + 1) :
    (p - 2) * p = (6 * j1 - 1) * (6 * j1 + 1) ∧ (6 * j1 - 1) * (6 * j1 + 1) = 36 * j1 ^ 2 - 1 := by
  obtain ⟨a, rfl⟩ : ∃ a, j1 = a + 1 := ⟨j1 - 1, by omega⟩
  subst hp6
  have e1 : 6 * (a + 1) + 1 - 2 = 6 * (a + 1) - 1 := by omega
  have e2 : 6 * (a + 1) - 1 = 6 * a + 5 := by omega
  have e3 : 36 * (a + 1) ^ 2 - 1 = (6 * a + 5) * (6 * a + 7) := by
    have : 36 * (a + 1) ^ 2 = (6 * a + 5) * (6 * a + 7) + 1 := by ring
    omega
  refine ⟨by rw [e1], ?_⟩
  rw [e2, e3]
  ring

/-- Equation (7): every prime `> 3` is `6j + 1` or `6j - 1` for some `j ≥ 1`. -/
theorem eq7 {p : ℕ} (hp : Nat.Prime p) (h3 : 3 < p) :
    ∃ j : ℕ, 1 ≤ j ∧ (p = 6 * j + 1 ∨ p + 1 = 6 * j) := by
  have h2 : ¬ 2 ∣ p := by
    intro hd
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hd
    omega
  have h3' : ¬ 3 ∣ p := by
    intro hd
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp hd
    omega
  have : p % 6 = 1 ∨ p % 6 = 5 := by omega
  rcases this with h | h
  · exact ⟨p / 6, by omega, Or.inl (by omega)⟩
  · exact ⟨p / 6 + 1, by omega, Or.inr (by omega)⟩

/-- `PrimeSixClass`: a prime larger than 3 is `1` or `5` modulo `6`. -/
def PrimeSixClass (p : ℕ) : Prop :=
  Nat.Prime p → 3 < p → p % 6 = 1 ∨ p % 6 = 5

theorem primeSixClass_all (p : ℕ) : PrimeSixClass p := by
  intro hp h3
  obtain ⟨j, hj, h | h⟩ := eq7 hp h3 <;> omega

/-- The twin-prime chain assumption of the article: for every `N ≥ 1`,
`p + 6 ∑_{i=1}^N k_i` and `p - 2 + 6 ∑_{i=1}^N k_i` are both prime. -/
def TwinChainAssumption (p : ℕ) (k : ℕ → ℕ) : Prop :=
  ∀ N, 1 ≤ N → Nat.Prime (p + 6 * S k N) ∧ Nat.Prime (p - 2 + 6 * S k N)

/-- The numbers of the chain, in terms of `j`: `p + 6 S_m = 6 j_(m+1) + 1` and
`p - 2 + 6 S_m = 6 j_(m+1) - 1`. -/
theorem chain_numbers {j k : ℕ → ℕ} (h : ChainRecurrence j k) {p : ℕ} (hj1 : 1 ≤ j 1)
    (hp6 : p = 6 * j 1 + 1) (m : ℕ) :
    p + 6 * S k m = 6 * j (m + 1) + 1 ∧ p - 2 + 6 * S k m = 6 * j (m + 1) - 1 := by
  have := chain_eq h m
  constructor <;> omega

/-- Equations (8) and (10) in general: for `q = p + 6 s`,
`X q = (q - 2) q + Y q - 6 s q`. -/
theorem eq_shift {X p : ℕ} {Y : ℤ} (hXY : (X : ℤ) = ((p : ℤ) - 2) + Y) (s : ℕ) :
    (X : ℤ) * (p + 6 * s) = (((p : ℤ) + 6 * s) - 2) * (p + 6 * s) + Y * (p + 6 * s)
      - 6 * s * (p + 6 * s) := by
  rw [hXY]; ring

/-- Equation (8). -/
theorem eq8 {X p : ℕ} {Y : ℤ} {k : ℕ → ℕ} (hXY : (X : ℤ) = ((p : ℤ) - 2) + Y) :
    (X : ℤ) * (p + 6 * k 1) = (((p : ℤ) + 6 * k 1) - 2) * (p + 6 * k 1)
      + Y * (p + 6 * k 1) - 6 * k 1 * (p + 6 * k 1) :=
  eq_shift hXY (k 1)

/-- Equation (10). -/
theorem eq10 {X p : ℕ} {Y : ℤ} {k : ℕ → ℕ} (hXY : (X : ℤ) = ((p : ℤ) - 2) + Y) :
    (X : ℤ) * (p + 6 * k 1 + 6 * k 2) = (((p : ℤ) + 6 * k 1 + 6 * k 2) - 2) * (p + 6 * k 1 + 6 * k 2)
      + Y * (p + 6 * k 1 + 6 * k 2) - (6 * k 1 + 6 * k 2) * (p + 6 * k 1 + 6 * k 2) := by
  have := eq_shift hXY (k 1 + k 2)
  push_cast at this
  linarith

/-- The product identity behind (9) and (11): `(q - 2) q = 36 j_(m+1)² - 1`. -/
theorem eq_product {j k : ℕ → ℕ} (h : ChainRecurrence j k) {p : ℕ} (hp6 : p = 6 * j 1 + 1)
    (m : ℕ) :
    (((p : ℤ) + 6 * S k m) - 2) * (p + 6 * S k m) = 36 * (j (m + 1) : ℤ) ^ 2 - 1 := by
  have := chain_eq h m
  have h' : (j (m + 1) : ℤ) = j 1 + S k m := by exact_mod_cast this
  rw [h', hp6]; push_cast; ring

/-- Equation (9). -/
theorem eq9 {j k : ℕ → ℕ} (h : ChainRecurrence j k) {p : ℕ} (hp6 : p = 6 * j 1 + 1) :
    (((p : ℤ) + 6 * k 1) - 2) * (p + 6 * k 1)
        = (6 * (j 1 : ℤ) + 6 * k 1 - 1) * (6 * (j 1 : ℤ) + 6 * k 1 + 1)
      ∧ (6 * (j 1 : ℤ) + 6 * k 1 - 1) * (6 * (j 1 : ℤ) + 6 * k 1 + 1)
        = (6 * (j 2 : ℤ) - 1) * (6 * (j 2 : ℤ) + 1)
      ∧ (6 * (j 2 : ℤ) - 1) * (6 * (j 2 : ℤ) + 1) = 36 * (j 2 : ℤ) ^ 2 - 1 := by
  have h2 : (j 2 : ℤ) = j 1 + k 1 := by
    have := h 1 le_rfl
    exact_mod_cast this
  refine ⟨?_, ?_, by ring⟩
  · rw [hp6]; push_cast; ring
  · rw [h2]; ring

/-- Equation (11). -/
theorem eq11 {j k : ℕ → ℕ} (h : ChainRecurrence j k) {p : ℕ} (hp6 : p = 6 * j 1 + 1) :
    (((p : ℤ) + 6 * k 1 + 6 * k 2) - 2) * (p + 6 * k 1 + 6 * k 2) = 36 * (j 3 : ℤ) ^ 2 - 1 := by
  have := eq_product h hp6 2
  have hS : S k 2 = k 1 + k 2 := by
    simp [S, Finset.sum_Icc_succ_top]
  rw [hS] at this
  push_cast at this
  linarith

/-- Equation (12) (with the quantities of the article, `N ≥ 1`). -/
theorem eq12 {X p : ℕ} {Y : ℤ} {j k : ℕ → ℕ} (h : ChainRecurrence j k)
    (hXY : (X : ℤ) = ((p : ℤ) - 2) + Y) (hp6 : p = 6 * j 1 + 1) {N : ℕ} (hN : 1 ≤ N) :
    (X : ℤ) * (N * p + 6 * ((∑ i ∈ Icc 1 (N - 1), (N - i) * k i : ℕ) : ℤ))
      = 36 * (∑ i ∈ Icc 1 N, ((j i : ℕ) : ℤ) ^ 2) - N
        + Y * (N * p + 6 * ((∑ i ∈ Icc 1 (N - 1), (N - i) * k i : ℕ) : ℤ))
        - 6 * p * ((∑ i ∈ Icc 1 (N - 1), (N - i) * k i : ℕ) : ℤ)
        - 36 * (∑ i ∈ Icc 1 (N - 1), (((∑ L ∈ Icc 1 i, k L : ℕ)) : ℤ) ^ 2) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have h18 := eq18_aux h n
  have hA := sum_Icc_one_split (fun i => (j i) ^ 2) n
  have h18z : ((∑ i ∈ Icc 2 (n + 1), (j i) ^ 2 : ℕ) : ℤ)
      = (n : ℤ) * (j 1 : ℤ) ^ 2 + 2 * (j 1 : ℤ) * (W k n : ℤ)
        + ∑ i ∈ Icc 1 n, ((S k i : ℕ) : ℤ) ^ 2 := by
    have := congrArg (fun x : ℕ => (x : ℤ)) h18
    push_cast at this ⊢
    exact this
  have hAz : ((∑ i ∈ Icc 1 (n + 1), (j i) ^ 2 : ℕ) : ℤ)
      = (j 1 : ℤ) ^ 2 + ((∑ i ∈ Icc 2 (n + 1), (j i) ^ 2 : ℕ) : ℤ) := by
    have := congrArg (fun x : ℕ => (x : ℤ)) hA
    push_cast at this ⊢
    exact this
  simp only [Nat.add_sub_cancel]
  have hW : (∑ i ∈ Icc 1 n, (n + 1 - i) * k i : ℕ) = W k n := rfl
  have hS : ∀ i, (∑ L ∈ Icc 1 i, k L : ℕ) = S k i := fun i => rfl
  simp only [hW, hS]
  push_cast at h18z hAz ⊢
  rw [hXY]
  subst hp6
  push_cast
  linear_combination (-36) * hAz + (-36) * h18z


/-! ## Section 2: the difference `H` and the average bounds (28)–(47) -/

/-- `k_max = Max {j_i - j_(i-1)}, i ≤ N`, i.e. the largest of `k_1, …, k_(N-1)`. -/
def MaxIncrement (k : ℕ → ℕ) (N : ℕ) : ℕ := (Icc 1 (N - 1)).sup k

lemma W_one (n : ℕ) : 2 * W (fun _ => 1) n = n * (n + 1) := by
  induction n with
  | zero => simp [W]
  | succ n ih =>
      have hS : S (fun _ => 1) (n + 1) = n + 1 := by simp [S]
      rw [W_succ, mul_add, ih, hS]
      ring

lemma W_le_of_bound {k : ℕ → ℕ} {n H : ℕ} (hk : ∀ i, 1 ≤ i → i ≤ n → k i ≤ H) :
    2 * W k n ≤ n * (n + 1) * H := by
  have h1 : W k n ≤ W (fun _ => 1) n * H := by
    unfold W
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    have hi' := Finset.mem_Icc.mp hi
    calc (n + 1 - i) * k i ≤ (n + 1 - i) * H := Nat.mul_le_mul_left _ (hk i hi'.1 hi'.2)
      _ = (n + 1 - i) * 1 * H := by ring
  calc 2 * W k n ≤ 2 * (W (fun _ => 1) n * H) := Nat.mul_le_mul_left _ h1
    _ = (2 * W (fun _ => 1) n) * H := by ring
    _ = n * (n + 1) * H := by rw [W_one]

/-- Equation (28), in `ℚ` (`N ≥ 2`). -/
theorem eq28 {j k : ℕ → ℕ} (h : ChainRecurrence j k) {N : ℕ} (hN : 2 ≤ N) :
    (∑ i ∈ Icc 2 N, (j i : ℚ)) / (N * (N - 1))
      = (j 1 : ℚ) / N + (∑ i ∈ Icc 1 (N - 1), ((N - i : ℕ) : ℚ) * k i) / (N * (N - 1)) := by
  have hN1 : 1 ≤ N := by omega
  have h23 := congrArg (fun x : ℕ => (x : ℚ)) (eq23 h hN1)
  push_cast [Nat.cast_sub hN1] at h23
  have hN0 : (N : ℚ) ≠ 0 := by
    have : (0 : ℚ) < N := by exact_mod_cast (by omega : 0 < N)
    exact this.ne'
  have hNm : (N : ℚ) - 1 ≠ 0 := by
    have : (1 : ℚ) < N := by exact_mod_cast (by omega : 1 < N)
    exact sub_ne_zero.mpr this.ne'
  rw [h23]
  field_simp

/-- Equation (29), natural-number form: `2 ∑ (N-i) k_i ≤ N (N-1) k_max`. -/
theorem eq29_nat (k : ℕ → ℕ) {N : ℕ} (hN : 1 ≤ N) :
    2 * ∑ i ∈ Icc 1 (N - 1), (N - i) * k i ≤ N * (N - 1) * MaxIncrement k N := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have := W_le_of_bound (k := k) (n := n) (H := MaxIncrement k (n + 1)) (by
    intro i hi1 hi2
    unfold MaxIncrement
    exact Finset.le_sup (f := k) (Finset.mem_Icc.mpr ⟨hi1, by simpa using hi2⟩))
  simpa [W, mul_comm] using this

/-- Equation (29): `∑_{i=1}^{N-1} (N-i) k_i ≤ N (N-1) / 2 · k_max`. -/
theorem eq29 (k : ℕ → ℕ) {N : ℕ} (hN : 1 ≤ N) :
    (∑ i ∈ Icc 1 (N - 1), ((N - i : ℕ) : ℚ) * k i)
      ≤ (N : ℚ) * (N - 1) / 2 * MaxIncrement k N := by
  have h' : ((2 * ∑ i ∈ Icc 1 (N - 1), (N - i) * k i : ℕ) : ℚ)
      ≤ ((N * (N - 1) * MaxIncrement k N : ℕ) : ℚ) := by exact_mod_cast eq29_nat k hN
  push_cast [Nat.cast_sub hN] at h'
  linarith

/-- The general averaged bound behind (30) and (34): if `k_i ≤ H` for `i ≤ N-1`, then
`∑_{i=2}^N j_i / (N (N-1)) ≤ j_1 / N + H / 2`. -/
theorem avg_bound {j k : ℕ → ℕ} (h : ChainRecurrence j k) {N H : ℕ} (hN : 2 ≤ N)
    (hk : ∀ i, 1 ≤ i → i ≤ N - 1 → k i ≤ H) :
    (∑ i ∈ Icc 2 N, (j i : ℚ)) / (N * (N - 1)) ≤ (j 1 : ℚ) / N + (H : ℚ) / 2 := by
  have hN1 : 1 ≤ N := by omega
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hW := W_le_of_bound (k := k) (n := n) (H := H) (by
    intro i hi1 hi2; exact hk i hi1 (by simpa using hi2))
  have hWq : (2 : ℚ) * (W k n : ℚ) ≤ n * (n + 1) * H := by exact_mod_cast hW
  have h23 := congrArg (fun x : ℕ => (x : ℚ)) (eq23 h hN1)
  simp only [Nat.add_sub_cancel] at h23
  push_cast at h23
  have hWdef : (∑ i ∈ Icc 1 n, ((n + 1 - i : ℕ) : ℚ) * k i) = (W k n : ℚ) := by
    unfold W; push_cast; rfl
  rw [hWdef] at h23
  have hn : (0 : ℚ) < n := by exact_mod_cast (by omega : 0 < n)
  have hpos : (0 : ℚ) < ((n + 1 : ℕ) : ℚ) * (((n + 1 : ℕ) : ℚ) - 1) := by
    push_cast; nlinarith
  rw [h23, div_le_iff₀ hpos]
  have e : ((j 1 : ℚ) / ((n + 1 : ℕ) : ℚ) + (H : ℚ) / 2)
      * (((n + 1 : ℕ) : ℚ) * (((n + 1 : ℕ) : ℚ) - 1))
      = (((n + 1 : ℕ) : ℚ) - 1) * j 1 + n * (n + 1) * H / 2 := by
    push_cast
    field_simp
    ring
  rw [e]
  push_cast
  linarith

/-- Equation (30): `∑_{i=2}^N j_i / (N (N-1)) ≤ j_1 / N + k_max / 2`. -/
theorem eq30 {j k : ℕ → ℕ} (h : ChainRecurrence j k) {N : ℕ} (hN : 2 ≤ N) :
    (∑ i ∈ Icc 2 N, (j i : ℚ)) / (N * (N - 1))
      ≤ (j 1 : ℚ) / N + (MaxIncrement k N : ℚ) / 2 :=
  avg_bound h hN (fun i hi1 hi2 =>
    Finset.le_sup (f := k) (Finset.mem_Icc.mpr ⟨hi1, hi2⟩))

/-- Equation (31): for each `N ≥ 2` there is `z` with `k_max = j_z - j_(z-1) = k_(z-1)`. -/
theorem eq31 {j k : ℕ → ℕ} (h : ChainRecurrence j k) {N : ℕ} (hN : 2 ≤ N) :
    ∃ z, 2 ≤ z ∧ z ≤ N ∧ MaxIncrement k N = j z - j (z - 1) ∧ j z - j (z - 1) = k (z - 1) := by
  have hne : (Icc 1 (N - 1)).Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
  obtain ⟨i, hi, hmax⟩ := Finset.exists_mem_eq_sup _ hne k
  have hi' := Finset.mem_Icc.mp hi
  have hst := h i hi'.1
  refine ⟨i + 1, by omega, by omega, ?_, ?_⟩
  · simp only [Nat.add_sub_cancel]
    unfold MaxIncrement
    rw [hmax]; omega
  · simp only [Nat.add_sub_cancel]; omega

/-- The article's `H = ∑_{i=1}^{z-1} k_i`. -/
def HQuantity (k : ℕ → ℕ) (z : ℕ) : ℕ := ∑ i ∈ Icc 1 (z - 1), k i

/-- The shifted chain: `J_1 = j_1` and `J_i = j_(z-2+i)` for `i > 1`. -/
def ShiftedChain (j : ℕ → ℕ) (z : ℕ) (i : ℕ) : ℕ :=
  if i = 1 then j 1 else j (z - 2 + i)

/-- Equation (32): `J_2 = H + j_1 = j_z`. -/
theorem eq32 {j k : ℕ → ℕ} (h : ChainRecurrence j k) {z : ℕ} (hz : 2 ≤ z) :
    ShiftedChain j z 2 = HQuantity k z + j 1 ∧ HQuantity k z + j 1 = j z
      ∧ ShiftedChain j z 1 = j 1 := by
  refine ⟨?_, ?_, by simp [ShiftedChain]⟩
  · have := chain_eq h (z - 1)
    have e : z - 1 + 1 = z := by omega
    rw [e] at this
    simp only [ShiftedChain, HQuantity]
    have e2 : z - 2 + 2 = z := by omega
    simp only [e2]
    unfold S at this
    simp
    omega
  · have := chain_eq h (z - 1)
    have e : z - 1 + 1 = z := by omega
    rw [e] at this
    unfold S at this
    unfold HQuantity
    omega

lemma sum_Icc_translate {M : Type*} [AddCommMonoid M] (f : ℕ → M) (c d : ℕ) :
    ∑ i ∈ Icc (c + 2) (c + 2 + d), f i = ∑ i ∈ Icc 2 (d + 2), f (c + i) := by
  induction d with
  | zero => simp
  | succ d ih =>
      have e1 : c + 2 + (d + 1) = (c + 2 + d) + 1 := by omega
      have e2 : d + 1 + 2 = (d + 2) + 1 := by omega
      rw [e1, e2, Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega), ih]
      have e3 : c + 2 + d + 1 = c + (d + 2 + 1) := by omega
      rw [e3]

/-- Equation (33): `∑_{i=z}^N j_i = ∑_{i=2}^M J_i` with `M = N - z + 2`. -/
theorem eq33 (j : ℕ → ℕ) {z N : ℕ} (hz : 2 ≤ z) (hzN : z ≤ N) :
    ∑ i ∈ Icc z N, j i = ∑ i ∈ Icc 2 (N - z + 2), ShiftedChain j z i := by
  obtain ⟨c, rfl⟩ : ∃ c, z = c + 2 := ⟨z - 2, by omega⟩
  obtain ⟨d, rfl⟩ : ∃ d, N = c + 2 + d := ⟨N - (c + 2), by omega⟩
  have e : c + 2 + d - (c + 2) + 2 = d + 2 := by omega
  rw [e, sum_Icc_translate j c d]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_Icc.mp hi
  have : i ≠ 1 := by omega
  simp [ShiftedChain, this]

/-- The shifted chain is monotone (used to apply the average bound to `J`). -/
theorem shifted_mono {j k : ℕ → ℕ} (h : ChainRecurrence j k) {z : ℕ} (hz : 2 ≤ z) :
    ∀ i, 1 ≤ i → ShiftedChain j z i ≤ ShiftedChain j z (i + 1) := by
  intro i hi
  by_cases h1 : i = 1
  · subst h1
    have := (eq32 h hz)
    have h2 : ShiftedChain j z (1 + 1) = j z := by
      have e : (1 + 1 : ℕ) = 2 := rfl
      rw [e]; rw [this.1, this.2.1]
    rw [h2, this.2.2]
    have := chain_mono h (a := 1) (b := z) le_rfl (by omega)
    exact this
  · have hne : i + 1 ≠ 1 := by omega
    simp only [ShiftedChain, h1, hne, if_false]
    have := h (z - 2 + i) (by omega)
    have e : z - 2 + (i + 1) = z - 2 + i + 1 := by omega
    rw [e]; omega

/-- Equation (34): the averaged bound for the shifted chain `J`
(hypothesis (47) bounds the increments of `J` by `H`; `J 2 = H + J 1`). -/
theorem eq34 {J : ℕ → ℕ} {H M : ℕ} (hM : 2 ≤ M)
    (hmono : ∀ i, 1 ≤ i → J i ≤ J (i + 1))
    (h1 : J 2 = H + J 1)
    (h47 : ∀ i, 2 < i → i ≤ M → J i - J (i - 1) ≤ H) :
    (∑ i ∈ Icc 2 M, (J i : ℚ)) / (M * (M - 1)) ≤ (J 1 : ℚ) / M + (H : ℚ) / 2 := by
  have hrec : ChainRecurrence J (fun i => J (i + 1) - J i) := by
    intro i hi
    have := hmono i hi
    simp only
    omega
  apply avg_bound hrec hM
  intro i hi hiM
  by_cases h2 : i = 1
  · subst h2
    show J 2 - J 1 ≤ H
    omega
  · have := h47 (i + 1) (by omega) (by omega)
    simpa using this

/-- Equation (35): if `L` is the least index with `H < J L - J (L-1)` (and `L > 2`),
then for `M < L` the increments up to `M` are bounded by `H`. -/
theorem eq35 {J : ℕ → ℕ} {H L M : ℕ}
    (hL : IsLeast {L : ℕ | 2 < L ∧ H < J L - J (L - 1)} L) (hM : M < L) :
    ∀ i, 2 < i → i ≤ M → J i - J (i - 1) ≤ H := by
  intro i hi hiM
  by_contra hcon
  have := hL.2 ⟨hi, Nat.lt_of_not_le hcon⟩
  omega

/-- Equations (36)–(40). Here `H = J 2 - j_1`, `J 1 = j_1`, and `(34)` is the hypothesis. -/
theorem eq36_to_40 {J : ℕ → ℕ} {j1 H M : ℕ} (hM : 2 ≤ M) (hJ1 : J 1 = j1)
    (hJ2 : j1 ≤ J 2) (hH : H = J 2 - j1)
    (h34 : (∑ i ∈ Icc 2 M, (J i : ℚ)) / (M * (M - 1)) ≤ (J 1 : ℚ) / M + (H : ℚ) / 2) :
    (∑ i ∈ Icc 3 M, (J i : ℚ)) / (M * (M - 1))
        ≤ (J 1 : ℚ) / M + ((J 2 : ℚ) - j1) / 2 - (J 2 : ℚ) / (M * (M - 1))                    -- (36)
    ∧ (∑ i ∈ Icc 3 M, (J i : ℚ)) / (M * (M - 1))
        ≤ (J 1 : ℚ) / M - (j1 : ℚ) / 2 + (J 2 : ℚ) * (1 / 2 - 1 / (M * (M - 1)))              -- (37)
    ∧ 2 * (∑ i ∈ Icc 3 M, (J i : ℚ)) / (2 * (M * (M - 1)))
        - (J 2 : ℚ) * ((M * (M - 1) - 2) / (2 * (M * (M - 1))))
        ≤ (j1 : ℚ) * (1 / M - 1 / 2)                                                        -- (38)
    ∧ (2 * (∑ i ∈ Icc 3 M, (J i : ℚ)) + 2 * (J 2 : ℚ)) / (2 * (M * (M - 1)))
        - (J 2 : ℚ) * ((M * (M - 1)) / (2 * (M * (M - 1))))
        ≤ (j1 : ℚ) * (1 / M - 1 / 2)                                                        -- (39)
    ∧ (∑ i ∈ Icc 2 M, (J i : ℚ)) / (M * (M - 1)) - (J 2 : ℚ) / 2
        ≤ (j1 : ℚ) * (1 / M - 1 / 2) := by                                                  -- (40)
  have hMq : (2 : ℚ) ≤ M := by exact_mod_cast hM
  have hMpos : (0 : ℚ) < M := by linarith
  have hM0 : (M : ℚ) ≠ 0 := hMpos.ne'
  have hM1 : (0 : ℚ) < (M : ℚ) - 1 := by linarith
  have hsplit : (∑ i ∈ Icc 2 M, (J i : ℚ)) = (J 2 : ℚ) + ∑ i ∈ Icc 3 M, (J i : ℚ) := by
    obtain ⟨n, rfl⟩ : ∃ n, M = n + 2 := ⟨M - 2, by omega⟩
    exact sum_Icc_two_split (fun i => (J i : ℚ)) n
  have hHq : (H : ℚ) = (J 2 : ℚ) - j1 := by
    rw [hH]; push_cast [Nat.cast_sub hJ2]; ring
  have hJ1q : (J 1 : ℚ) = j1 := by exact_mod_cast hJ1
  have ha : (0 : ℚ) < (M : ℚ) * ((M : ℚ) - 1) := mul_pos hMpos hM1
  have ha0 : (M : ℚ) * ((M : ℚ) - 1) ≠ 0 := ha.ne'
  have h34' : (J 2 : ℚ) / ((M : ℚ) * ((M : ℚ) - 1))
      + (∑ i ∈ Icc 3 M, (J i : ℚ)) / ((M : ℚ) * ((M : ℚ) - 1))
      ≤ (j1 : ℚ) / M + ((J 2 : ℚ) - j1) / 2 := by
    have := h34
    rw [hsplit, add_div, hHq, hJ1q] at this
    exact this
  have e36 : (∑ i ∈ Icc 3 M, (J i : ℚ)) / ((M : ℚ) * ((M : ℚ) - 1))
      ≤ (J 1 : ℚ) / M + ((J 2 : ℚ) - j1) / 2 - (J 2 : ℚ) / ((M : ℚ) * ((M : ℚ) - 1)) := by
    rw [hJ1q]; linarith
  have e37 : (∑ i ∈ Icc 3 M, (J i : ℚ)) / ((M : ℚ) * ((M : ℚ) - 1))
      ≤ (J 1 : ℚ) / M - (j1 : ℚ) / 2
        + (J 2 : ℚ) * (1 / 2 - 1 / ((M : ℚ) * ((M : ℚ) - 1))) := by
    have e : (J 2 : ℚ) * (1 / 2 - 1 / ((M : ℚ) * ((M : ℚ) - 1)))
        = (J 2 : ℚ) / 2 - (J 2 : ℚ) / ((M : ℚ) * ((M : ℚ) - 1)) := by ring
    rw [e, hJ1q]; linarith
  have e38 : 2 * (∑ i ∈ Icc 3 M, (J i : ℚ)) / (2 * ((M : ℚ) * ((M : ℚ) - 1)))
        - (J 2 : ℚ) * (((M : ℚ) * ((M : ℚ) - 1) - 2) / (2 * ((M : ℚ) * ((M : ℚ) - 1))))
        ≤ (j1 : ℚ) * (1 / M - 1 / 2) := by
    have h1 : 2 * (∑ i ∈ Icc 3 M, (J i : ℚ)) / (2 * ((M : ℚ) * ((M : ℚ) - 1)))
        = (∑ i ∈ Icc 3 M, (J i : ℚ)) / ((M : ℚ) * ((M : ℚ) - 1)) := by
      field_simp
    have h2 : (J 2 : ℚ) * (((M : ℚ) * ((M : ℚ) - 1) - 2) / (2 * ((M : ℚ) * ((M : ℚ) - 1))))
        = (J 2 : ℚ) * (1 / 2 - 1 / ((M : ℚ) * ((M : ℚ) - 1))) := by
      field_simp
    have h3 : (j1 : ℚ) * (1 / M - 1 / 2) = (j1 : ℚ) / M - (j1 : ℚ) / 2 := by ring
    rw [h1, h2, h3]
    rw [hJ1q] at e37
    linarith
  have e39 : (2 * (∑ i ∈ Icc 3 M, (J i : ℚ)) + 2 * (J 2 : ℚ)) / (2 * ((M : ℚ) * ((M : ℚ) - 1)))
        - (J 2 : ℚ) * (((M : ℚ) * ((M : ℚ) - 1)) / (2 * ((M : ℚ) * ((M : ℚ) - 1))))
      = 2 * (∑ i ∈ Icc 3 M, (J i : ℚ)) / (2 * ((M : ℚ) * ((M : ℚ) - 1)))
        - (J 2 : ℚ) * (((M : ℚ) * ((M : ℚ) - 1) - 2) / (2 * ((M : ℚ) * ((M : ℚ) - 1)))) := by
    field_simp
    ring
  have e40 : (∑ i ∈ Icc 2 M, (J i : ℚ)) / ((M : ℚ) * ((M : ℚ) - 1)) - (J 2 : ℚ) / 2
      = (2 * (∑ i ∈ Icc 3 M, (J i : ℚ)) + 2 * (J 2 : ℚ)) / (2 * ((M : ℚ) * ((M : ℚ) - 1)))
        - (J 2 : ℚ) * (((M : ℚ) * ((M : ℚ) - 1)) / (2 * ((M : ℚ) * ((M : ℚ) - 1)))) := by
    rw [hsplit]
    field_simp
    ring
  refine ⟨e36, e37, e38, ?_, ?_⟩
  · rw [e39]; exact e38
  · rw [e40, e39]; exact e38

/-- Equation (41): for `M > 2` (and `j_1 > 0`), `∑_{i=2}^M J_i / (M (M-1)) < J_2 / 2`. -/
theorem eq41 {J : ℕ → ℕ} {H j1 M : ℕ} (hM : 2 < M) (hj1 : 0 < j1) (hJ1 : J 1 = j1)
    (hJ2 : j1 ≤ J 2) (hH : H = J 2 - j1)
    (h34 : (∑ i ∈ Icc 2 M, (J i : ℚ)) / (M * (M - 1)) ≤ (J 1 : ℚ) / M + (H : ℚ) / 2) :
    (∑ i ∈ Icc 2 M, (J i : ℚ)) / (M * (M - 1)) < (J 2 : ℚ) / 2 := by
  have h40 := (eq36_to_40 (by omega) hJ1 hJ2 hH h34).2.2.2.2
  have hMq : (2 : ℚ) < M := by exact_mod_cast hM
  have hlt : (1 : ℚ) / M < 1 / 2 := one_div_lt_one_div_of_lt (by norm_num) hMq
  have hneg : (j1 : ℚ) * (1 / M - 1 / 2) < 0 :=
    mul_neg_of_pos_of_neg (by exact_mod_cast hj1) (by linarith)
  linarith

/-- Equations (42) and (43): `∑_{i=2}^M J_i / (J_2 M (M-1)) < 1/2` for `M > 2`. -/
theorem eq42 {J : ℕ → ℕ} {M : ℕ} (hM : 2 < M) (hJ2 : 0 < J 2)
    (h41 : (∑ i ∈ Icc 2 M, (J i : ℚ)) / (M * (M - 1)) < (J 2 : ℚ) / 2) :
    (∑ i ∈ Icc 2 M, (J i : ℚ)) / (J 2 * M * (M - 1)) < 1 / 2 := by
  have hMq : (2 : ℚ) < M := by exact_mod_cast hM
  have ha : (0 : ℚ) < (M : ℚ) * ((M : ℚ) - 1) := mul_pos (by linarith) (by linarith)
  have hJ : (0 : ℚ) < J 2 := by exact_mod_cast hJ2
  have h1 := (div_lt_iff₀ ha).mp h41
  have e : (J 2 : ℚ) * M * ((M : ℚ) - 1) = (J 2 : ℚ) * ((M : ℚ) * ((M : ℚ) - 1)) := by ring
  rw [e, div_lt_iff₀ (mul_pos hJ ha)]
  linarith

theorem eq43 {J : ℕ → ℕ} {M : ℕ} (hM : 2 < M) (hJ2 : 0 < J 2)
    (h41 : (∑ i ∈ Icc 2 M, (J i : ℚ)) / (M * (M - 1)) < (J 2 : ℚ) / 2) :
    (∑ i ∈ Icc 2 M, (J i : ℚ)) / (J 2 * M * (M - 1)) < 1 / 2 :=
  eq42 hM hJ2 h41

/-- Equation (44), from (42) at `M = 3`. -/
theorem eq44_of_eq42 {J : ℕ → ℕ} (hJ2 : 0 < J 2)
    (h : (∑ i ∈ Icc 2 3, (J i : ℚ)) / (J 2 * 3 * (3 - 1)) < 1 / 2) :
    J 2 + J 3 < 3 * J 2 ∧ J 3 < 2 * J 2 := by
  have hs : (∑ i ∈ Icc 2 3, (J i : ℚ)) = (J 2 : ℚ) + J 3 := by
    rw [show Icc 2 3 = {2, 3} by decide]; simp
  rw [hs] at h
  have hJ : (0 : ℚ) < J 2 := by exact_mod_cast hJ2
  rw [div_lt_iff₀ (by positivity)] at h
  have h' : ((J 2 + J 3 : ℕ) : ℚ) < ((3 * J 2 : ℕ) : ℚ) := by push_cast; linarith
  have := Nat.cast_lt.mp h'
  omega

/-- Equation (44): if `M = 3` is possible (`J_3 - J_2 ≤ H`, `J_2 = H + j_1`, `j_1 > 0`), then
`J_2 + J_3 < 3 J_2` and `J_3 < 2 J_2`. The whole chain (34) → (41) → (42) is used. -/
theorem eq44 {J : ℕ → ℕ} {H : ℕ} (hmono : ∀ i, 1 ≤ i → J i ≤ J (i + 1))
    (hj1 : 0 < J 1) (h1 : J 2 = H + J 1) (h3 : J 3 - J 2 ≤ H) :
    J 2 + J 3 < 3 * J 2 ∧ J 3 < 2 * J 2 := by
  have h47 : ∀ i, 2 < i → i ≤ 3 → J i - J (i - 1) ≤ H := by
    intro i hi hi3
    have : i = 3 := by omega
    subst this; simpa using h3
  have h34 := eq34 (J := J) (H := H) (M := 3) (by norm_num) hmono h1 h47
  have hJ2 : J 1 ≤ J 2 := by omega
  have h41 := eq41 (J := J) (j1 := J 1) (H := H) (M := 3) (by norm_num) hj1 rfl hJ2
    (by omega) (by simpa using h34)
  have h42 := eq42 (J := J) (M := 3) (by norm_num) (by omega) h41
  exact eq44_of_eq42 (by omega) (by simpa using h42)

/-- Equation (45): `J_3 < 2 J_2` and `J_3 → ∞` imply `J_2 → ∞`. -/
def TendsToInfinity (a : ℕ → ℕ) : Prop := ∀ B : ℕ, ∃ n : ℕ, ∀ m : ℕ, n ≤ m → B < a m

theorem eq45 {J2 J3 : ℕ → ℕ} (h : ∀ z, J3 z < 2 * J2 z) (h3 : TendsToInfinity J3) :
    TendsToInfinity J2 := by
  intro B
  obtain ⟨n, hn⟩ := h3 (2 * B)
  exact ⟨n, fun m hm => by have := hn m hm; have := h m; omega⟩

/-- Equation (46): the reduced `H`, `∑_{i=1}^{z-2} k_i`, satisfies `H' + j_1 = j_(z-1)`. -/
def HReduced (k : ℕ → ℕ) (z : ℕ) : ℕ := ∑ i ∈ Icc 1 (z - 2), k i

theorem eq46 {j k : ℕ → ℕ} (h : ChainRecurrence j k) {z : ℕ} (hz : 2 ≤ z) :
    HReduced k z + j 1 = j (z - 1) := by
  have := chain_eq h (z - 2)
  have e : z - 2 + 1 = z - 1 := by omega
  rw [e] at this
  unfold S at this
  unfold HReduced
  omega

/-- The hypothesis "`M = 3` is always possible", for the chain: for every `z ≥ 2`,
`J_3 - J_2 = k_z ≤ H = j_z - j_1`. -/
def AlwaysM3 (j k : ℕ → ℕ) : Prop := ∀ z, 2 ≤ z → k z ≤ j z - j 1

/-- Consequence of (44) along the chain: if `M = 3` is always possible then
`j_(z+1) < 2 j_z` for every `z ≥ 2`. -/
theorem alwaysM3_implies {j k : ℕ → ℕ} (hc : Chain j k) (hM3 : AlwaysM3 j k) :
    ∀ z, 2 ≤ z → j (z + 1) < 2 * j z := by
  intro z hz
  have hJ := eq32 hc.step hz
  have hmono := shifted_mono hc.step hz
  have hH : j z = HQuantity k z + j 1 := hJ.2.1.symm
  have hj1 : 0 < ShiftedChain j z 1 := by rw [hJ.2.2]; exact hc.j_pos 1 le_rfl
  have h1 : ShiftedChain j z 2 = HQuantity k z + ShiftedChain j z 1 := by
    rw [hJ.2.2]; exact hJ.1
  have hk := hM3 z hz
  have h3 : ShiftedChain j z 3 - ShiftedChain j z 2 ≤ HQuantity k z := by
    have e3 : ShiftedChain j z 3 = j (z + 1) := by
      simp [ShiftedChain]; congr 1; omega
    have e2 : ShiftedChain j z 2 = j z := hJ.1.trans hJ.2.1
    rw [e3, e2]
    have := hc.step z (by omega)
    omega
  have := (eq44 hmono hj1 h1 h3).2
  have e3 : ShiftedChain j z 3 = j (z + 1) := by
    simp [ShiftedChain]; congr 1; omega
  have e2 : ShiftedChain j z 2 = j z := hJ.1.trans hJ.2.1
  rw [e3, e2] at this
  exact this

/-- The article's closing remark of Section 2: if some `G` has `j_(G+1) ≥ 2 j_G`, then
`M = 3` cannot always be possible (so the conjecture "may be true"). -/
def ExistsG (j : ℕ → ℕ) : Prop := ∃ G, 2 ≤ G ∧ 2 * j G ≤ j (G + 1)

theorem not_alwaysM3_of_existsG {j k : ℕ → ℕ} (hc : Chain j k) (hG : ExistsG j) :
    ¬ AlwaysM3 j k := by
  intro hM3
  obtain ⟨G, hG2, hGle⟩ := hG
  have := alwaysM3_implies hc hM3 G hG2
  omega


/-! ## The "Important Remark" and equations (25)–(27) -/

/-- Three consecutive odd numbers larger than 3 are never all prime
(one of them is divisible by 3). -/
theorem no_three_consecutive_odd_primes {n : ℕ} (hn : 3 < n) :
    ¬ (Nat.Prime n ∧ Nat.Prime (n + 2) ∧ Nat.Prime (n + 4)) := by
  rintro ⟨h1, h2, h3⟩
  have key : ∀ m, Nat.Prime m → 3 < m → ¬ 3 ∣ m := by
    intro m hm hm3 hd
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hm).mp hd
    omega
  have a := key n h1 hn
  have b := key (n + 2) h2 (by omega)
  have c := key (n + 4) h3 (by omega)
  omega

/-- Equation (25): `q = 6 j_i + 1 = 6 j_(i+1) - 1` would force `j_(i+1) - j_i = 2/6`,
i.e. `k_i = 1/3`. -/
theorem eq25 {a b : ℚ} (h : 6 * a + 1 = 6 * b - 1) : b - a = 2 / 6 ∧ b - a = 1 / 3 :=
  ⟨by linarith, by linarith⟩

/-- `1/3` is not a natural number, so no such natural `k_i` exists. -/
theorem eq25_no_natural : ¬ ∃ k : ℕ, (k : ℚ) = 1 / 3 := by
  rintro ⟨k, hk⟩
  have h : (3 * k : ℚ) = 1 := by rw [hk]; norm_num
  have h' : 3 * k = 1 := by exact_mod_cast h
  omega

/-- Equivalent integer form: no naturals `a`, `b ≥ 1` with `6a + 1 = 6b - 1`. -/
theorem eq25_no_shared_role : ¬ ∃ a b : ℕ, 1 ≤ b ∧ 6 * a + 1 = 6 * b - 1 := by
  rintro ⟨a, b, hb, h⟩
  omega

/-- Equation (26): with `k_i = 1/3`, `q + 6 k_i = q + 2`, which differs from `q + n` for `n > 2`. -/
theorem eq26 {q n : ℕ} (hn : 2 < n) : (q : ℚ) + 6 * (1 / 3) = q + 2 ∧ q + 2 ≠ q + n := by
  refine ⟨by norm_num, by omega⟩

/-- Equation (27): after twin primes `q, q + 2` (with `q > 3`) the next prime exceeds `q + 4`. -/
theorem eq27 {q p : ℕ} (hq : Nat.Prime q) (h3 : 3 < q) (hq2 : Nat.Prime (q + 2))
    (hp : Nat.Prime p) (hlt : q + 2 < p) : q + 4 < p := by
  have hno := no_three_consecutive_odd_primes h3
  have hq_odd : ¬ 2 ∣ q := fun hd => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).mp hd
    omega
  by_contra hcon
  have hcases : p = q + 3 ∨ p = q + 4 := by omega
  rcases hcases with rfl | rfl
  · have h2 : 2 ∣ q + 3 := by omega
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2
    omega
  · exact hno ⟨hq, hq2, hp⟩

/-! ## Section 3: iterated indices, Brun's bound, the twin-prime counting function -/

instance : DecidablePred TwinPair := fun p => by unfold TwinPair; infer_instance

/-- `π₂(y)`: the number of twin-prime pairs `(p, p+2)` with `p ≤ y`. -/
def TwinPrimeCount (y : ℕ) : ℕ := ((Icc 1 y).filter TwinPair).card

/-- The number of twin-prime pairs `(p, p+2)` with `p < m`. -/
def TwinCountBelow (m : ℕ) : ℕ := ((range m).filter TwinPair).card

/-- The article's `s`: the finite number of twin primes smaller than `6 j_1 - 1`. -/
def sOf (j : ℕ → ℕ) : ℕ := TwinCountBelow (6 * j 1 - 1)

/-- If `x → ∞` then `j_x → ∞` (the chain is at least the identity). -/
theorem tendsToInfinity_comp_chain {j k : ℕ → ℕ} (h : Chain j k) {xs : ℕ → ℕ}
    (hx : ∀ n, 1 ≤ xs n) (hinf : TendsToInfinity xs) :
    TendsToInfinity (fun n => j (xs n)) := by
  intro B
  obtain ⟨n, hn⟩ := hinf B
  exact ⟨n, fun m hm => lt_of_lt_of_le (hn m hm) (chain_ge_index h (hx m))⟩

/-- The iterate `(j, x)^t` of equation (48). -/
def idxIter (j : ℕ → ℕ) (x t : ℕ) : ℕ := j^[t] x

theorem idxIter_zero (j : ℕ → ℕ) (x : ℕ) : idxIter j x 0 = x := rfl
theorem idxIter_one (j : ℕ → ℕ) (x : ℕ) : idxIter j x 1 = j x := rfl
theorem idxIter_two (j : ℕ → ℕ) (x : ℕ) : idxIter j x 2 = j (j x) := rfl
theorem idxIter_three (j : ℕ → ℕ) (x : ℕ) : idxIter j x 3 = j (j (j x)) := rfl
theorem idxIter_succ (j : ℕ → ℕ) (x t : ℕ) : idxIter j x (t + 1) = j (idxIter j x t) :=
  Function.iterate_succ_apply' j t x

/-- `(j, x)^t → ∞` as `t → ∞` (consequence the article draws from the conjecture). -/
def IterDiverges (j : ℕ → ℕ) (x : ℕ) : Prop := TendsToInfinity (fun t => idxIter j x t)

/-- The article's "logical mathematical induction of indices": if `(j, x)^t → ∞`
then, peeling off the `t` layers, `x → ∞`.  (Recorded as the article's inference;
`x → ∞` for a fixed `x` is the constant sequence tending to infinity.) -/
def IndexInductionClaim (j : ℕ → ℕ) : Prop :=
  ∀ x, IterDiverges j x → TendsToInfinity (fun _ : ℕ => x)

/-- The contradiction drawn in Section 3: a fixed (finite) `x` cannot tend to infinity. -/
theorem not_tendsToInfinity_const (x : ℕ) : ¬ TendsToInfinity (fun _ : ℕ => x) := by
  intro h
  obtain ⟨n, hn⟩ := h x
  exact lt_irrefl _ (hn n le_rfl)

theorem not_iterDiverges_of_indexInduction {j : ℕ → ℕ} (hI : IndexInductionClaim j) (x : ℕ) :
    ¬ IterDiverges j x :=
  fun hd => not_tendsToInfinity_const x (hI x hd)

/-- "`j_x` approaches infinity although `x` is finite", rendered as: `6 j_x + 1` is at least
every finite bound `y`. -/
def FiniteIndexInfiniteValue (j : ℕ → ℕ) (x : ℕ) : Prop := ∀ y : ℕ, y ≤ 6 * j x + 1

/-- The inequality (50), obtained in the article from Brun's bound together with the claim that
the chain gathers all the twin primes: `6 j_{[(π₂(y) - s)/2]} + 1 < y`. -/
def Claim50 (j : ℕ → ℕ) (y : ℕ) : Prop :=
  6 * j ((TwinPrimeCount y - sOf j) / 2) + 1 < y

/-- Equation (51): for `x < [(π₂(y) - s)/2]`, `6 j_x + 1 < y`. -/
theorem eq51 {j k : ℕ → ℕ} (h : ChainRecurrence j k) {x y : ℕ} (hx : 1 ≤ x)
    (h50 : Claim50 j y) (hxlt : x < (TwinPrimeCount y - sOf j) / 2) : 6 * j x + 1 < y := by
  have := chain_mono h hx hxlt.le
  unfold Claim50 at h50
  omega

/-- Equation (52): if `j_x` is beyond every finite `y`, then `x ≥ [(π₂(y) - s)/2]` for every `y`. -/
theorem eq52 {j k : ℕ → ℕ} (h : ChainRecurrence j k) {x : ℕ} (hx : 1 ≤ x)
    (hinf : FiniteIndexInfiniteValue j x) (h50 : ∀ y, Claim50 j y) :
    ∀ y, (TwinPrimeCount y - sOf j) / 2 ≤ x := by
  intro y
  by_contra hc
  have h1 := eq51 h hx (h50 y) (Nat.lt_of_not_le hc)
  have h2 := hinf y
  omega

/-! ## Brun's bound (49), the twin-prime constant, and (53) -/

/-- Brun's upper bound (49): for some constant `E`, `π₂(y) < E · y / (log y)²`. -/
def BrunUpperBound : Prop :=
  ∃ E : ℝ, ∀ y : ℕ, 2 ≤ y → (TwinPrimeCount y : ℝ) < E * (y : ℝ) / (Real.log (y : ℝ)) ^ 2

/-- Equation (53), the algebraic part: for `j ≥ 1`,
`1/(6j-1) + 1/(6j+1) = 12 j / (36 j² - 1) > 1/(3 j)`. -/
theorem eq53 {j : ℕ} (hj : 1 ≤ j) :
    (1 : ℚ) / (6 * j - 1) + 1 / (6 * j + 1) = 12 * j / (36 * (j : ℚ) ^ 2 - 1)
      ∧ (1 : ℚ) / (3 * j) < 12 * j / (36 * (j : ℚ) ^ 2 - 1) := by
  have hj' : (1 : ℚ) ≤ j := by exact_mod_cast hj
  have h1 : (0 : ℚ) < 6 * j - 1 := by linarith
  have h2 : (0 : ℚ) < 6 * j + 1 := by linarith
  have h3 : (0 : ℚ) < 36 * (j : ℚ) ^ 2 - 1 := by nlinarith
  have hjpos : (0 : ℚ) < j := by linarith
  constructor
  · rw [div_add_div _ _ h1.ne' h2.ne']
    have e : (6 * (j : ℚ) - 1) * (6 * j + 1) = 36 * (j : ℚ) ^ 2 - 1 := by ring
    rw [e]
    congr 1
    ring
  · have e : (1 : ℚ) / (3 * j) = 12 * j / (36 * (j : ℚ) ^ 2) := by
      field_simp
      ring
    rw [e]
    apply div_lt_div_of_pos_left (by positivity) h3
    linarith

/-- The reciprocal-series claim of the annex: `∑_{i=2}^N 1/j_i` converges to a finite `R`. -/
def ReciprocalChainSeriesConverges (j : ℕ → ℕ) : Prop :=
  ∃ R : ℝ, Filter.Tendsto (fun N : ℕ => ∑ i ∈ Icc 2 N, (1 : ℝ) / (j i : ℝ))
    Filter.atTop (nhds R)

/-- Brun's theorem (the cited fact behind the annex): the sum of reciprocals of twin primes
converges. -/
def BrunConstantConverges : Prop :=
  Summable (fun p : ℕ => if TwinPair p then (1 : ℝ) / p + 1 / ((p + 2 : ℕ) : ℝ) else 0)

/-- The twin-prime constant `C₂ = ∏_{p ≥ 3} (1 - 1/(p-1)²)`. -/
noncomputable def twinPrimeConstant : ℝ :=
  ∏' p : {p : ℕ // Nat.Prime p ∧ 3 ≤ p}, (1 - 1 / ((p.1 : ℝ) - 1) ^ 2)

/-- The numerical remark of the conclusion: `2 C₂ ≈ 1.32032367…`. -/
def TwinPrimeConstantValueRemark : Prop :=
  |2 * twinPrimeConstant - 1.32032367| < 1 / 10 ^ 7

/-- The Hardy–Littlewood twin-prime conjecture (quantitative form):
`π₂(y) ∼ 2 C₂ · y / (log y)²`. -/
def HardyLittlewoodTwinPrime : Prop :=
  Filter.Tendsto
    (fun y : ℕ => (TwinPrimeCount y : ℝ) / (2 * twinPrimeConstant * y / (Real.log y) ^ 2))
    Filter.atTop (nhds 1)

/-! ## Twin primes, Siegel zeros and the claim ledger -/

/-- Infinitely many twin-prime pairs. -/
def InfinitelyManyTwinPairs : Prop := ∀ B : ℕ, ∃ p : ℕ, B < p ∧ TwinPair p

/-- The article's conclusion: the twin primes form a finite set. -/
def ClaimNoTwinPrimesBeyondFiniteSet : Prop := ∃ B : ℕ, ∀ p : ℕ, B < p → ¬ TwinPair p

theorem not_infinitelyMany_iff :
    ¬ InfinitelyManyTwinPairs ↔ ClaimNoTwinPrimesBeyondFiniteSet := by
  unfold InfinitelyManyTwinPairs ClaimNoTwinPrimesBeyondFiniteSet
  constructor
  · intro h
    by_contra hne
    exact h (fun B => by
      by_contra hB
      exact hne ⟨B, fun p hp hp' => hB ⟨p, hp, hp'⟩⟩)
  · rintro ⟨B, hB⟩ h
    obtain ⟨p, hp, hp'⟩ := h B
    exact hB p hp hp'

/-- The article's claim about the chain: the set of numbers `p - 2 + 6 ∑_{i ≤ N} k_i`
(the lower members of the chain's twin pairs) is not infinite. -/
def ClaimChainSetNotInfinite (p : ℕ) (k : ℕ → ℕ) : Prop :=
  ¬ Set.Infinite {q : ℕ | ∃ N, 1 ≤ N ∧ q = p - 2 + 6 * S k N}

/-- ... and the twin pairs not expressible through the chain form a finite set. -/
def ClaimComplementFinite (p : ℕ) (k : ℕ → ℕ) : Prop :=
  Set.Finite {q : ℕ | TwinPair q ∧ ¬ ∃ N, 1 ≤ N ∧ q = p - 2 + 6 * S k N}

/-- The claim that Hardy–Littlewood's quantitative conjecture fails. -/
def ClaimHardyLittlewoodFails : Prop := ¬ HardyLittlewoodTwinPrime

/-- Heath-Brown's theorem (1983), as quoted in the article: at least one of
"there are no Siegel zeros" and "there are infinitely many twin primes" holds.
`NoSiegelZeros` is an abstract proposition (Siegel zeros are not defined in Mathlib). -/
def HeathBrownStatement (NoSiegelZeros : Prop) : Prop :=
  NoSiegelZeros ∨ InfinitelyManyTwinPairs

theorem no_siegel_zeros_of_not_infinitelyMany {NoSiegelZeros : Prop}
    (hHB : HeathBrownStatement NoSiegelZeros) (hNoTwins : ¬ InfinitelyManyTwinPairs) :
    NoSiegelZeros :=
  hHB.resolve_right hNoTwins

/-- The article's last logical step: from its conclusion about twin primes and
Heath-Brown's dichotomy, there are no Siegel zeros. -/
theorem article_siegel_consequence {NoSiegelZeros : Prop}
    (hHB : HeathBrownStatement NoSiegelZeros) (hclaim : ClaimNoTwinPrimesBeyondFiniteSet) :
    NoSiegelZeros :=
  no_siegel_zeros_of_not_infinitelyMany hHB (not_infinitelyMany_iff.mpr hclaim)

/-- The two principal claims of the article (recorded as propositions, not asserted). -/
def ArticleSummaryClaims (NoSiegelZeros : Prop) : Prop :=
  ClaimNoTwinPrimesBeyondFiniteSet ∧ NoSiegelZeros


/-! ## The logical skeleton of the argument, and what is proved about it

The article's argument has this shape.

1. Build one increasing chain `j₁ < j₂ < …` (`j_(i+1) = j_i + k_i`, `k_i ≥ 1`) such that
   `(6 j_i - 1, 6 j_i + 1)` are twin primes, and assume it gathers all twin primes `> 3`
   (`ClaimChainSetNotInfinite` / `ChainGathersAllTwins`).
2. Algebra on the chain (all proved above): (4)–(24), (28)–(47).
3. If the twin-prime conjecture holds, the article asserts there is a finite index `x`
   whose value `j_x` is beyond every finite bound (`ArticleStepA`).
4. Brun's bound plus step 1 give `6 j_{[(π₂(y)-s)/2]} + 1 < y` for every `y` (`Claim50`).
5. Then `x ≥ [(π₂(y) - s)/2]` for every `y` (equation (52), proved above), while
   `π₂(y) → ∞` if the conjecture holds: contradiction.

Steps 1, 3 and 4 are the article's unproved inputs; they are explicit hypotheses below.
Step 5 and everything else is proved in Lean. -/

/-- The chain "gathers all twin primes above 3": every twin pair `(q, q+2)` with
`q ≥ 6 j₁ - 1` is `(6 j_i - 1, 6 j_i + 1)` for some `i ≥ 1`. -/
def ChainGathersAllTwins (j : ℕ → ℕ) : Prop :=
  ∀ q, 6 * j 1 - 1 ≤ q → TwinPair q → ∃ i, 1 ≤ i ∧ q = 6 * j i - 1

/-- The article's step 3. -/
def ArticleStepA (j : ℕ → ℕ) : Prop :=
  InfinitelyManyTwinPairs → ∃ x, 1 ≤ x ∧ FiniteIndexInfiniteValue j x

lemma twinPrimeCount_succ_of_pair {y p : ℕ} (hp : TwinPair p) (hy : y < p) :
    TwinPrimeCount y < TwinPrimeCount p := by
  unfold TwinPrimeCount
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨p, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hp.1.one_lt.le, le_rfl⟩, hp⟩
    · simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_Icc] at hq ⊢
    exact ⟨⟨hq.1.1, by omega⟩, hq.2⟩

/-- If there are infinitely many twin pairs, `π₂` is unbounded. -/
theorem twinPrimeCount_unbounded (h : InfinitelyManyTwinPairs) :
    ∀ M, ∃ y, M < TwinPrimeCount y := by
  intro M
  induction M with
  | zero =>
      obtain ⟨p, _, hp⟩ := h 0
      refine ⟨p, ?_⟩
      unfold TwinPrimeCount
      apply Finset.card_pos.mpr
      exact ⟨p, by simp only [Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨hp.1.one_lt.le, le_rfl⟩, hp⟩⟩
  | succ M ih =>
      obtain ⟨y, hy⟩ := ih
      obtain ⟨p, hpy, hp⟩ := h y
      exact ⟨p, lt_of_le_of_lt hy.le (twinPrimeCount_succ_of_pair hp hpy) |> fun _ =>
        lt_of_lt_of_le (Nat.succ_lt_succ hy) (Nat.succ_le_of_lt (twinPrimeCount_succ_of_pair hp hpy))⟩

/-- **The core deduction of the article** (steps 3–5): from the chain recurrence, step 3 and
step 4 (`Claim50` for every `y`), the twin primes are finite. -/
theorem article_core {j k : ℕ → ℕ} (h : ChainRecurrence j k)
    (hA : ArticleStepA j) (h50 : ∀ y, Claim50 j y) : ¬ InfinitelyManyTwinPairs := by
  intro hinf
  obtain ⟨x, hx, hxinf⟩ := hA hinf
  have h52 := eq52 h hx hxinf h50
  obtain ⟨y, hy⟩ := twinPrimeCount_unbounded hinf (2 * x + sOf j + 2)
  have := h52 y
  omega

/-- The article's full conclusion, from its explicit inputs and Heath-Brown's theorem. -/
theorem article_full {j k : ℕ → ℕ} {NoSiegelZeros : Prop} (h : ChainRecurrence j k)
    (hA : ArticleStepA j) (h50 : ∀ y, Claim50 j y) (hHB : HeathBrownStatement NoSiegelZeros) :
    ClaimNoTwinPrimesBeyondFiniteSet ∧ NoSiegelZeros :=
  ⟨not_infinitelyMany_iff.mp (article_core h hA h50),
   no_siegel_zeros_of_not_infinitelyMany hHB (article_core h hA h50)⟩

/-- Consistency check: the chain-numbers set is infinite when all `k_i ≥ 1`, so the
article's sentence "this set is not infinite" cannot hold under its own hypotheses. -/
theorem chain_set_infinite {k : ℕ → ℕ} (p : ℕ) (hk : ∀ i, 1 ≤ i → 0 < k i) :
    Set.Infinite {q : ℕ | ∃ N, 1 ≤ N ∧ q = p - 2 + 6 * S k N} := by
  have hS : ∀ N, N ≤ S k N := by
    intro N
    induction N with
    | zero => simp [S]
    | succ n ih => rw [S_succ]; have := hk (n + 1) (by omega); omega
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  have hmem : p - 2 + 6 * S k (B + 1) ∈ {q : ℕ | ∃ N, 1 ≤ N ∧ q = p - 2 + 6 * S k N} :=
    ⟨B + 1, by omega, rfl⟩
  have h1 := hB hmem
  have h2 := hS (B + 1)
  omega

theorem article_chain_claim_inconsistent (p : ℕ) (k : ℕ → ℕ) (hk : ∀ i, 1 ≤ i → 0 < k i) :
    ¬ ClaimChainSetNotInfinite p k := fun h => h (chain_set_infinite p hk)

end LouizTwinPrimeArticle
