/-
  Collatz_Louiz_Lean4_Complete_Translation.lean

  Lean 4 / Mathlib formalisation of the article by Akram Louiz on the Collatz conjecture
  (exponent sequences `p_i`, first and second final forms, padding / non-uniqueness,
  inclusion of the five forms, the infinite families of Section 7 and its corollaries,
  the appendix sequence `k_n`, and the Section 8 argument for the numbers 4B+1 and 4B-1).

  The file is self-contained (it does not need the PDF): the Collatz map, the functions
  `Phi`, the two final forms and every lemma are defined and proved here, with no unfinished proofs.
  The only assumption used anywhere is the explicit hypothesis `Article161` of
  Section 8 (statement (161) of the article), which appears as a hypothesis of
  `section8_166` and `section8_conclusion`.
-/
import Mathlib

set_option autoImplicit false


namespace LouizCollatz

open Finset

/-! ## 0. The Collatz map and "respecting the conjecture" -/

/-- The Collatz map: `n ↦ n/2` for even `n`, `n ↦ 3n+1` for odd `n`. -/
def collatzStep (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- A number "respects the Collatz conjecture" when its trajectory reaches `1`. -/
def ReachesOne (x : ℕ) : Prop := ∃ t : ℕ, collatzStep^[t] x = 1

/-- The Collatz conjecture: every strictly positive natural number reaches `1`. -/
def CollatzConjecture : Prop := ∀ x : ℕ, 1 ≤ x → ReachesOne x

lemma collatzStep_two_mul (n : ℕ) : collatzStep (2 * n) = n := by
  unfold collatzStep; simp

lemma collatzStep_odd {n : ℕ} (h : n % 2 = 1) : collatzStep n = 3 * n + 1 := by
  unfold collatzStep; simp [h]

/-- `e` successive halvings of `2^e * y` give `y`. -/
lemma iter_halve (e y : ℕ) : collatzStep^[e] (2 ^ e * y) = y := by
  induction e with
  | zero => simp
  | succ e ih =>
      rw [Function.iterate_succ_apply]
      have h : 2 ^ (e + 1) * y = 2 * (2 ^ e * y) := by ring
      rw [h, collatzStep_two_mul, ih]

/-- If `x` is odd and `3x + 1 = 2^e y` with `y` reaching `1`, so does `x`. -/
lemma reachesOne_of_step {x e y : ℕ} (hx : x % 2 = 1) (h : 3 * x + 1 = 2 ^ e * y)
    (hy : ReachesOne y) : ReachesOne x := by
  obtain ⟨t, ht⟩ := hy
  refine ⟨t + (e + 1), ?_⟩
  rw [Function.iterate_add_apply, Function.iterate_succ_apply, collatzStep_odd hx, h,
    iter_halve, ht]

lemma reachesOne_two_pow_mul {m : ℕ} (a : ℕ) (hm : ReachesOne m) : ReachesOne (2 ^ a * m) := by
  obtain ⟨t, ht⟩ := hm
  refine ⟨t + a, ?_⟩
  rw [Function.iterate_add_apply, iter_halve, ht]

lemma reachesOne_of_two_pow_mul {m : ℕ} (a : ℕ) (hm : 1 ≤ m) (h : ReachesOne (2 ^ a * m)) :
    ReachesOne m := by
  obtain ⟨t, ht⟩ := h
  by_cases hta : a ≤ t
  · obtain ⟨u, rfl⟩ : ∃ u, t = u + a := ⟨t - a, by omega⟩
    rw [Function.iterate_add_apply, iter_halve] at ht
    exact ⟨u, ht⟩
  · exfalso
    have e1 : 2 ^ a * m = 2 ^ t * (2 ^ (a - t) * m) := by
      rw [← mul_assoc, ← pow_add]; congr 2; omega
    rw [e1, iter_halve] at ht
    have h2 : 2 ∣ 2 ^ (a - t) * m := dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) m
    rw [ht] at h2
    omega

/-! ## 1. The exponent sums of the article -/

/-- `tail p N j = ∑_{i=j}^{N} p_i`. -/
def tail (p : ℕ → ℕ) (N j : ℕ) : ℕ := ∑ i ∈ Icc j N, p i

/-- The right-hand side of both final forms:
`2^{∑_{i=0}^N p_i} - ∑_{j=1}^N 3^{j-1} 2^{∑_{i=j}^N p_i}`  (in `ℤ`). -/
def Phi (p : ℕ → ℕ) (N : ℕ) : ℤ :=
  2 ^ (tail p N 0) - ∑ j ∈ Icc 1 N, 3 ^ (j - 1) * 2 ^ (tail p N j)

/-- The article's conditions on the exponents: `p_0 = 2A` with `A ≥ 1`, and `p_i ≥ 1`
for every `i ≥ 1`. -/
def ValidExp (p : ℕ → ℕ) : Prop := (∃ A, 1 ≤ A ∧ p 0 = 2 * A) ∧ ∀ i, 1 ≤ i → 1 ≤ p i

lemma ValidExp.p_pos {p : ℕ → ℕ} (h : ValidExp p) (i : ℕ) : 1 ≤ p i := by
  cases i with
  | zero => obtain ⟨⟨A, hA, h0⟩, _⟩ := h; omega
  | succ i => exact h.2 _ (by omega)

lemma tail_succ (p : ℕ → ℕ) (N j : ℕ) (hj : j ≤ N + 1) :
    tail p (N + 1) j = tail p N j + p (N + 1) := by
  unfold tail; rw [Finset.sum_Icc_succ_top hj]

lemma Phi_zero (p : ℕ → ℕ) : Phi p 0 = 2 ^ (p 0) := by simp [Phi, tail]

/-- The Horner-type recursion behind everything:
`Φ_{N+1} = 2^{p_{N+1}} (Φ_N - 3^N)`. -/
lemma Phi_succ (p : ℕ → ℕ) (N : ℕ) :
    Phi p (N + 1) = 2 ^ (p (N + 1)) * (Phi p N - 3 ^ N) := by
  unfold Phi
  rw [Finset.sum_Icc_succ_top (by omega)]
  have h0 : tail p (N + 1) 0 = tail p N 0 + p (N + 1) := tail_succ p N 0 (by omega)
  have h1 : tail p (N + 1) (N + 1) = p (N + 1) := by simp [tail]
  have h2 : ∀ j ∈ Icc 1 N, (3 : ℤ) ^ (j - 1) * 2 ^ (tail p (N + 1) j)
      = 2 ^ (p (N + 1)) * (3 ^ (j - 1) * 2 ^ (tail p N j)) := by
    intro j hj
    have := Finset.mem_Icc.mp hj
    rw [tail_succ p N j (by omega), pow_add]; ring
  rw [Finset.sum_congr rfl h2, ← Finset.mul_sum, h0, h1]
  simp only [Nat.add_sub_cancel]
  rw [pow_add]; ring

lemma Phi_congr {p q : ℕ → ℕ} {N : ℕ} (h : ∀ i, i ≤ N → p i = q i) : Phi p N = Phi q N := by
  have ht : ∀ j, tail p N j = tail q N j := by
    intro j; unfold tail
    exact Finset.sum_congr rfl (fun i hi => h i (Finset.mem_Icc.mp hi).2)
  unfold Phi; simp only [ht]

lemma phi_even {p : ℕ → ℕ} (h : ValidExp p) (N : ℕ) : (2 : ℤ) ∣ Phi p N := by
  cases N with
  | zero => rw [Phi_zero]; exact dvd_pow_self 2 (by have := h.p_pos 0; omega)
  | succ N =>
      rw [Phi_succ]
      exact Dvd.dvd.mul_right (dvd_pow_self 2 (by have := h.p_pos (N + 1); omega)) _

/-- The first final form: `3^{N+1} x + 3^N = Φ_N`. -/
def FirstFinalForm (x N : ℕ) (p : ℕ → ℕ) : Prop :=
  ValidExp p ∧ (3 : ℤ) ^ (N + 1) * x + 3 ^ N = Phi p N

/-- The second final form: `3^M x = Φ_M`. -/
def SecondFinalForm (x M : ℕ) (p : ℕ → ℕ) : Prop :=
  ValidExp p ∧ (3 : ℤ) ^ M * x = Phi p M

lemma form_odd {x N : ℕ} {p : ℕ → ℕ} (h : FirstFinalForm x N p) : x % 2 = 1 ∧ 1 ≤ x := by
  obtain ⟨hv, heq⟩ := h
  have h2 : (2 : ℤ) ∣ 3 ^ N * (3 * x + 1) := by
    have := phi_even hv N
    rw [← heq] at this
    have e : (3 : ℤ) ^ (N + 1) * x + 3 ^ N = 3 ^ N * (3 * x + 1) := by ring
    rwa [e] at this
  rcases Int.prime_two.dvd_or_dvd h2 with h3 | h3
  · have := Int.prime_two.dvd_of_dvd_pow h3
    omega
  · omega

/-- Core of the "peeling" step. -/
lemma peel_aux {p : ℕ → ℕ} (hv : ValidExp p) (N : ℕ) (z : ℤ) (hz0 : 0 ≤ z)
    (h : (3 : ℤ) ^ (N + 1) * z = Phi p (N + 1)) :
    ∃ yz : ℤ, z = 2 ^ (p (N + 1)) * yz ∧ (3 : ℤ) ^ (N + 1) * yz = Phi p N - 3 ^ N
      ∧ 1 ≤ yz ∧ yz % 2 = 1 := by
  rw [Phi_succ] at h
  have he1 : 1 ≤ p (N + 1) := hv.p_pos _
  have hBodd : Odd (Phi p N - 3 ^ N) :=
    (even_iff_two_dvd.mpr (phi_even hv N)).sub_odd (Odd.pow (by decide))
  have hcop : IsCoprime ((2 : ℤ) ^ (p (N + 1))) (3 ^ (N + 1)) := by
    apply IsCoprime.pow
    exact ⟨-1, 1, by norm_num⟩
  have hdvd : (2 : ℤ) ^ (p (N + 1)) ∣ z :=
    hcop.dvd_of_dvd_mul_left ⟨Phi p N - 3 ^ N, h⟩
  obtain ⟨yz, hy⟩ := hdvd
  have hyz : (3 : ℤ) ^ (N + 1) * yz = Phi p N - 3 ^ N := by
    have : (2 : ℤ) ^ (p (N + 1)) * (3 ^ (N + 1) * yz)
        = 2 ^ (p (N + 1)) * (Phi p N - 3 ^ N) := by
      rw [← h, hy]; ring
    exact mul_left_cancel₀ (by positivity) this
  have hyodd : Odd yz := by
    have : Odd ((3 : ℤ) ^ (N + 1) * yz) := by rw [hyz]; exact hBodd
    exact (Int.odd_mul.mp this).2
  have hy0 : 0 ≤ yz := by
    by_contra hneg0
    have hneg : yz < 0 := not_le.mp hneg0
    have : (2 : ℤ) ^ (p (N + 1)) * yz < 0 := mul_neg_of_pos_of_neg (by positivity) hneg
    linarith
  have hodd' : yz % 2 = 1 := Int.odd_iff.mp hyodd
  exact ⟨yz, hy, hyz, by omega, hodd'⟩

/-- Peeling the last exponent of the first final form: one odd Collatz step. -/
lemma peel {x N : ℕ} {p : ℕ → ℕ} (h : FirstFinalForm x (N + 1) p) :
    ∃ y : ℕ, 3 * x + 1 = 2 ^ (p (N + 1)) * y ∧ y % 2 = 1 ∧ FirstFinalForm y N p := by
  obtain ⟨hv, heq⟩ := h
  obtain ⟨yz, hy, hyz, hy1, hyodd⟩ := peel_aux hv N (3 * x + 1) (by positivity)
    (by rw [← heq]; ring)
  lift yz to ℕ using (by omega)
  refine ⟨yz, by exact_mod_cast hy, by omega, hv, ?_⟩
  linarith

/-- Peeling the second final form. -/
lemma second_peel {x M : ℕ} {p : ℕ → ℕ} (h : SecondFinalForm x (M + 1) p) :
    ∃ y : ℕ, x = 2 ^ (p (M + 1)) * y ∧ y % 2 = 1 ∧ FirstFinalForm y M p := by
  obtain ⟨hv, heq⟩ := h
  obtain ⟨yz, hy, hyz, hy1, hyodd⟩ := peel_aux hv M (x : ℤ) (by positivity) heq
  lift yz to ℕ using (by omega)
  refine ⟨yz, by exact_mod_cast hy, by omega, hv, ?_⟩
  linarith

/-- (⇐) A number with a first final form reaches `1`. -/
theorem reachesOne_of_form : ∀ (N x : ℕ) (p : ℕ → ℕ), FirstFinalForm x N p → ReachesOne x := by
  intro N
  induction N with
  | zero =>
      intro x p h
      obtain ⟨hx, _⟩ := form_odd h
      have h2 := h.2
      rw [Phi_zero] at h2
      have h' : 3 * x + 1 = 2 ^ (p 0) * 1 := by
        have : (3 : ℤ) * x + 1 = 2 ^ (p 0) := by simpa using h2
        have : (3 * x + 1 : ℕ) = 2 ^ (p 0) := by exact_mod_cast this
        omega
      exact reachesOne_of_step hx h' ⟨0, rfl⟩
  | succ N ih =>
      intro x p h
      obtain ⟨hx, _⟩ := form_odd h
      obtain ⟨y, hy, _, hf⟩ := peel h
      exact reachesOne_of_step hx hy (ih y p hf)

/-- (⇒) An odd number reaching `1` has a first final form. -/
theorem exists_form_of_reaches :
    ∀ (t x : ℕ), x % 2 = 1 → collatzStep^[t] x = 1 → ∃ N p, FirstFinalForm x N p := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro x hx ht
    by_cases hx1 : x = 1
    · subst hx1
      refine ⟨0, fun _ => 2, ⟨⟨1, le_rfl, rfl⟩, fun i _ => by norm_num⟩, ?_⟩
      rw [Phi_zero]; norm_num
    · have hxpos : 0 < x := by omega
      obtain ⟨e, y, hyodd, hdec⟩ := Nat.exists_eq_two_pow_mul_odd (show 3 * x + 1 ≠ 0 by omega)
      have hyodd' : y % 2 = 1 := Nat.odd_iff.mp hyodd
      have he : 1 ≤ e := by
        rcases Nat.eq_zero_or_pos e with h0 | h0
        · subst h0; simp at hdec; omega
        · exact h0
      obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := by
        rcases Nat.eq_zero_or_pos t with h0 | h0
        · subst h0; simp at ht; exact absurd ht hx1
        · exact ⟨t - 1, by omega⟩
      rw [Function.iterate_succ_apply, collatzStep_odd hx, hdec] at ht
      have hes : e ≤ s := by
        by_contra hlt
        have e1 : 2 ^ e * y = 2 ^ s * (2 ^ (e - s) * y) := by
          rw [← mul_assoc, ← pow_add]; congr 2; omega
        rw [e1, iter_halve] at ht
        have h2 : 2 ∣ 2 ^ (e - s) * y := dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) y
        rw [ht] at h2
        omega
      obtain ⟨u, rfl⟩ : ∃ u, s = u + e := ⟨s - e, by omega⟩
      rw [Function.iterate_add_apply, iter_halve] at ht
      obtain ⟨N', p', hf⟩ := ih u (by omega) y hyodd' ht
      refine ⟨N' + 1, fun i => if i = N' + 1 then e else p' i, ?_⟩
      obtain ⟨⟨A, hA, h0⟩, hpos⟩ := hf.1
      refine ⟨⟨⟨A, hA, by simpa using h0⟩, fun i hi => ?_⟩, ?_⟩
      · by_cases hi' : i = N' + 1
        · simp [hi']; exact he
        · simp [hi']; exact hpos i hi
      · have hc : Phi (fun i => if i = N' + 1 then e else p' i) N' = Phi p' N' :=
          Phi_congr (fun i hi => by simp; omega)
        rw [Phi_succ, hc]
        simp only [ite_true]
        have hdecz : (3 : ℤ) * x + 1 = 2 ^ e * y := by exact_mod_cast hdec
        have hf2 := hf.2
        rw [← hf2]
        linear_combination (3 : ℤ) ^ (N' + 1) * hdecz


/-! ## 2. Padding: non-uniqueness of the final forms (Section 3) -/

/-- The sequence `q_k = 2` for `k < O`, `q_k = p_(k-O)` for `k ≥ O`. -/
def shiftSeq (p : ℕ → ℕ) (O k : ℕ) : ℕ := if k < O then 2 else p (k - O)

lemma Phi_two (m : ℕ) : Phi (fun _ => 2) m = 4 * 3 ^ m := by
  induction m with
  | zero => simp [Phi_zero]
  | succ m ih => rw [Phi_succ, ih]; norm_num; ring

lemma Phi_shift (p : ℕ → ℕ) (O : ℕ) : ∀ N, Phi (shiftSeq p O) (N + O) = 3 ^ O * Phi p N := by
  intro N
  induction N with
  | zero =>
      simp only [Nat.zero_add]
      rcases Nat.eq_zero_or_pos O with h0 | hpos
      · subst h0; simp [shiftSeq, Phi_zero]
      · obtain ⟨O', rfl⟩ : ∃ O', O = O' + 1 := ⟨O - 1, by omega⟩
        rw [Phi_succ]
        have hq : shiftSeq p (O' + 1) (O' + 1) = p 0 := by simp [shiftSeq]
        have hc : Phi (shiftSeq p (O' + 1)) O' = Phi (fun _ => 2) O' :=
          Phi_congr (fun i hi => by simp [shiftSeq]; omega)
        rw [hq, hc, Phi_two, Phi_zero]; ring
  | succ N ih =>
      have e : N + 1 + O = (N + O) + 1 := by omega
      rw [e, Phi_succ, ih]
      have hq : shiftSeq p O (N + O + 1) = p (N + 1) := by
        unfold shiftSeq; rw [if_neg (by omega)]; congr 1; omega
      rw [hq, Phi_succ]; ring

lemma validExp_shift {p : ℕ → ℕ} (h : ValidExp p) (O : ℕ) : ValidExp (shiftSeq p O) := by
  obtain ⟨⟨A, hA, h0⟩, hpos⟩ := h
  refine ⟨?_, fun i hi => ?_⟩
  · by_cases hO : 0 < O
    · exact ⟨1, le_rfl, by simp [shiftSeq, hO]⟩
    · exact ⟨A, hA, by simp [shiftSeq, hO, h0]⟩
  · unfold shiftSeq
    split_ifs with hlt
    · omega
    · by_cases hz : i - O = 0
      · rw [hz]; omega
      · exact hpos _ (by omega)

/-- Section 3: from one first final form we get one for every larger `N`
(`q_k = 2` for `k < O`, `q_(k+O) = p_k`). -/
theorem form_shift {x N : ℕ} {p : ℕ → ℕ} (h : FirstFinalForm x N p) (O : ℕ) :
    FirstFinalForm x (N + O) (shiftSeq p O) := by
  refine ⟨validExp_shift h.1 O, ?_⟩
  rw [Phi_shift, ← h.2]
  have : (3 : ℤ) ^ (N + O + 1) = 3 ^ O * 3 ^ (N + 1) := by ring
  rw [this, pow_add]; ring

theorem second_form_shift {x M : ℕ} {p : ℕ → ℕ} (h : SecondFinalForm x M p) (O : ℕ) :
    SecondFinalForm x (M + O) (shiftSeq p O) := by
  refine ⟨validExp_shift h.1 O, ?_⟩
  rw [Phi_shift, ← h.2, pow_add]; ring

/-! ## 3. Equivalence of the final forms with the Collatz conjecture (Section 6) -/

theorem odd_reachesOne_iff_form {x : ℕ} (hx : x % 2 = 1) :
    ReachesOne x ↔ ∃ N p, FirstFinalForm x N p := by
  constructor
  · rintro ⟨t, ht⟩; exact exists_form_of_reaches t x hx ht
  · rintro ⟨N, p, h⟩; exact reachesOne_of_form N x p h

theorem odd_reachesOne_iff_form_ge_two {x : ℕ} (hx : x % 2 = 1) :
    ReachesOne x ↔ ∃ N, 2 ≤ N ∧ ∃ p, FirstFinalForm x N p := by
  rw [odd_reachesOne_iff_form hx]
  constructor
  · rintro ⟨N, p, h⟩; exact ⟨N + 2, by omega, _, form_shift h 2⟩
  · rintro ⟨N, _, p, h⟩; exact ⟨N, p, h⟩

lemma second_of_first {y N q : ℕ} {p : ℕ → ℕ} (hq : 1 ≤ q) (h : FirstFinalForm y N p) :
    SecondFinalForm (2 ^ q * y) (N + 1) (fun i => if i = N + 1 then q else p i) := by
  obtain ⟨⟨⟨A, hA, h0⟩, hpos⟩, heq⟩ := h
  refine ⟨⟨⟨A, hA, by simpa using h0⟩, fun i hi => ?_⟩, ?_⟩
  · by_cases hi' : i = N + 1
    · simp [hi']; exact hq
    · simp [hi']; exact hpos i hi
  · have hc : Phi (fun i => if i = N + 1 then q else p i) N = Phi p N :=
      Phi_congr (fun i hi => by simp; omega)
    rw [Phi_succ, hc]
    simp only [ite_true]
    push_cast
    linear_combination (2 : ℤ) ^ q * heq

theorem even_reachesOne_iff_second_form {x : ℕ} (hx : x % 2 = 0) (hx1 : 1 ≤ x) :
    ReachesOne x ↔ ∃ M, 2 ≤ M ∧ ∃ p, SecondFinalForm x M p := by
  constructor
  · intro h
    obtain ⟨a, m, hm, hdec⟩ := Nat.exists_eq_two_pow_mul_odd (show x ≠ 0 by omega)
    have hm' : m % 2 = 1 := Nat.odd_iff.mp hm
    have hm1 : 1 ≤ m := by omega
    have ha : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with h0 | h0
      · subst h0; simp at hdec; omega
      · exact h0
    rw [hdec] at h
    have hr : ReachesOne m := reachesOne_of_two_pow_mul a hm1 h
    obtain ⟨N, p, hf⟩ := (odd_reachesOne_iff_form hm').mp hr
    have hs := second_of_first ha hf
    rw [← hdec] at hs
    exact ⟨N + 1 + 2, by omega, _, second_form_shift hs 2⟩
  · rintro ⟨M, hM, p, h⟩
    obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
    obtain ⟨y, hy, hyodd, hf⟩ := second_peel h
    rw [hy]
    exact reachesOne_two_pow_mul _ (reachesOne_of_form M' y p hf)

/-- Section 6: the conjecture is equivalent to "every odd number has a first final form
(with `N ≥ 2`)". -/
theorem collatz_iff_odd_first_form :
    CollatzConjecture ↔ ∀ x : ℕ, x % 2 = 1 → ∃ N, 2 ≤ N ∧ ∃ p, FirstFinalForm x N p := by
  constructor
  · intro h x hx
    exact (odd_reachesOne_iff_form_ge_two hx).mp (h x (by omega))
  · intro h x hx
    obtain ⟨a, m, hm, hdec⟩ := Nat.exists_eq_two_pow_mul_odd (show x ≠ 0 by omega)
    have hm' : m % 2 = 1 := Nat.odd_iff.mp hm
    rw [hdec]
    exact reachesOne_two_pow_mul a ((odd_reachesOne_iff_form_ge_two hm').mpr (h m hm'))

/-- Section 6: odd numbers have the first final form, even numbers the second. -/
theorem collatz_iff_final_forms :
    CollatzConjecture ↔
      (∀ x : ℕ, x % 2 = 1 → ∃ N, 2 ≤ N ∧ ∃ p, FirstFinalForm x N p) ∧
      (∀ x : ℕ, x % 2 = 0 → 1 ≤ x → ∃ M, 2 ≤ M ∧ ∃ p, SecondFinalForm x M p) := by
  constructor
  · intro h
    refine ⟨collatz_iff_odd_first_form.mp h, fun x hx hx1 => ?_⟩
    exact (even_reachesOne_iff_second_form hx hx1).mp (h x hx1)
  · rintro ⟨h1, _⟩
    exact collatz_iff_odd_first_form.mpr h1

/-! ## 4. Uniqueness up to padding (Section 3) -/

lemma two_pow_mul_odd_inj {a b u v : ℕ} (hu : u % 2 = 1) (hv : v % 2 = 1)
    (h : 2 ^ a * u = 2 ^ b * v) : a = b ∧ u = v := by
  induction a generalizing b with
  | zero =>
      rcases b with _ | b
      · simpa using h
      · exfalso
        have : 2 ∣ u := by
          have : u = 2 ^ (b + 1) * v := by simpa using h
          rw [this]; exact dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) v
        omega
  | succ a ih =>
      rcases b with _ | b
      · exfalso
        have : 2 ∣ v := by
          have : 2 ^ (a + 1) * u = v := by simpa using h
          rw [← this]; exact dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) u
        omega
      · have h' : 2 ^ a * u = 2 ^ b * v := by
          have : 2 * (2 ^ a * u) = 2 * (2 ^ b * v) := by
            rw [← mul_assoc, ← mul_assoc, ← pow_succ', ← pow_succ']; exact h
          omega
        obtain ⟨h1, h2⟩ := ih h'
        exact ⟨by omega, h2⟩

lemma form_one_all_two : ∀ (K : ℕ) (q : ℕ → ℕ), FirstFinalForm 1 K q → ∀ i, i ≤ K → q i = 2 := by
  intro K
  induction K with
  | zero =>
      intro q h i hi
      have h2 := h.2
      rw [Phi_zero] at h2
      norm_num at h2
      have h3 : (4 : ℕ) = 2 ^ (q 0) := by
        have : (4 : ℤ) = 2 ^ (q 0) := by linarith
        exact_mod_cast this
      have : q 0 = 2 := by
        have := Nat.pow_right_injective (le_refl 2) (show 2 ^ 2 = 2 ^ (q 0) by simpa using h3)
        omega
      have hi0 : i = 0 := by omega
      subst hi0; exact this
  | succ K ih =>
      intro q h i hi
      obtain ⟨y, hy, hyodd, hf⟩ := peel h
      have h4 : 2 ^ 2 * 1 = 2 ^ (q (K + 1)) * y := by simpa using hy
      obtain ⟨he, hyy⟩ := two_pow_mul_odd_inj (by norm_num) hyodd h4
      subst hyy
      by_cases hiK : i = K + 1
      · subst hiK; omega
      · exact ih q hf i (by omega)

/-- Section 3 (uniqueness part): two first final forms of the same number are related by
padding: `q_k = 2` for `k < M - N`, and `q_(M-N+k) = p_k` for `0 ≤ k ≤ N`. -/
theorem form_unique : ∀ (N M x : ℕ) (p q : ℕ → ℕ), N ≤ M →
    FirstFinalForm x N p → FirstFinalForm x M q →
    (∀ i, i < M - N → q i = 2) ∧ ∀ k, k ≤ N → q (M - N + k) = p k := by
  intro N
  induction N with
  | zero =>
      intro M x p q _ hp hq
      rcases M with _ | M
      · refine ⟨fun i hi => by omega, fun k hk => ?_⟩
        have hk0 : k = 0 := by omega
        subst hk0
        have h1 := hp.2; have h2 := hq.2
        rw [Phi_zero] at h1 h2
        have e : (2 : ℤ) ^ (p 0) = 2 ^ (q 0) := by rw [← h1, ← h2]
        have e' : (2 : ℕ) ^ (p 0) = 2 ^ (q 0) := by exact_mod_cast e
        have := Nat.pow_right_injective (le_refl 2) e'
        simpa using this.symm
      · obtain ⟨y, hy, hyodd, hf⟩ := peel hq
        have h1 := hp.2
        rw [Phi_zero] at h1
        have h3 : 3 * x + 1 = 2 ^ (p 0) * 1 := by
          have : (3 : ℤ) * x + 1 = 2 ^ (p 0) := by simpa using h1
          have : (3 * x + 1 : ℕ) = 2 ^ (p 0) := by exact_mod_cast this
          omega
        have h4 : 2 ^ (p 0) * 1 = 2 ^ (q (M + 1)) * y := h3.symm.trans hy
        obtain ⟨he, hyy⟩ := two_pow_mul_odd_inj (by norm_num) hyodd h4
        subst hyy
        refine ⟨fun i hi => form_one_all_two M q hf i (by omega), fun k hk => ?_⟩
        have hk0 : k = 0 := by omega
        subst hk0
        simpa using he.symm
  | succ N ih =>
      intro M x p q hNM hp hq
      obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
      obtain ⟨y1, hy1, hodd1, hf1⟩ := peel hp
      obtain ⟨y2, hy2, hodd2, hf2⟩ := peel hq
      obtain ⟨he, hyy⟩ := two_pow_mul_odd_inj hodd1 hodd2 (hy1.symm.trans hy2)
      subst hyy
      obtain ⟨hA, hB⟩ := ih M' y1 p q (by omega) hf1 hf2
      refine ⟨fun i hi => hA i (by omega), fun k hk => ?_⟩
      by_cases hkN : k = N + 1
      · subst hkN
        have : M' + 1 - (N + 1) + (N + 1) = M' + 1 := by omega
        rw [this]; exact he.symm
      · have : M' + 1 - (N + 1) + k = M' - N + k := by omega
        rw [this]; exact hB k (by omega)

/-- Section 3: infinitely many different expressions: the paddings by `O ≥ 1` are all
different expressions of the same number. -/
theorem infinitely_many_expressions {x N : ℕ} {p : ℕ → ℕ} (h : FirstFinalForm x N p) :
    ∀ O, FirstFinalForm x (N + O) (shiftSeq p O) := fun O => form_shift h O

/-! ## 5. The five forms of the introduction and their inclusion (Sections 2, 4, 5) -/

/-- Fourth form: `n` even, `n ≥ 2`. -/
def FourthForm (n x : ℕ) (p : ℕ → ℕ) : Prop :=
  n % 2 = 0 ∧ 2 ≤ n ∧ ValidExp p ∧ (3 : ℤ) ^ (n / 2 + 1) * x + 3 ^ (n / 2) = Phi p (n / 2)

/-- Fifth form: `n` odd, `n ≥ 2`. -/
def FifthForm (n x : ℕ) (p : ℕ → ℕ) : Prop :=
  n % 2 = 1 ∧ 2 ≤ n ∧ ValidExp p ∧ (3 : ℤ) ^ ((n + 1) / 2) * x = Phi p ((n + 1) / 2)

/-- The five forms of the introduction (the third with `p₁ ≥ 1`, written without subtraction). -/
def FiveForms (x : ℕ) : Prop :=
  (∃ M, 1 ≤ M ∧ x = 2 ^ M) ∨
  (∃ M, 1 ≤ M ∧ 3 * x + 1 = 2 ^ (2 * M)) ∨
  (∃ M p1, 1 ≤ M ∧ 1 ≤ p1 ∧ 3 * x + 2 ^ p1 = 2 ^ (2 * M + p1)) ∨
  (∃ n p, FourthForm n x p) ∨
  (∃ n p, FifthForm n x p)

/-- From the equivalences: every number reaching `1` is in (at least) one of the five forms. -/
theorem fiveForms_of_reachesOne {x : ℕ} (hx1 : 1 ≤ x) (h : ReachesOne x) : FiveForms x := by
  rcases Nat.mod_two_eq_zero_or_one x with hx | hx
  · obtain ⟨M, hM, p, hf⟩ := (even_reachesOne_iff_second_form hx hx1).mp h
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨2 * M - 1, p, by omega, by omega, hf.1, ?_⟩)))
    have : (2 * M - 1 + 1) / 2 = M := by omega
    rw [this]; exact hf.2
  · obtain ⟨N, hN, p, hf⟩ := (odd_reachesOne_iff_form_ge_two hx).mp h
    refine Or.inr (Or.inr (Or.inr (Or.inl ⟨2 * N, p, by omega, by omega, hf.1, ?_⟩)))
    have : 2 * N / 2 = N := by omega
    rw [this]; exact hf.2


/-! ## 6. Sections 2, 4, 5: the first, second and third forms are included in the fourth/fifth -/

lemma four_pow_eq_two_pow (B : ℕ) : (4 : ℕ) ^ B = 2 ^ (2 * B) := by
  rw [pow_mul]; norm_num

lemma pow_four_eq (D : ℕ) : (2 : ℤ) ^ (2 * D) = 4 ^ D := by
  rw [pow_mul]; norm_num

/-- Equation (98): `4^N = 1 + 3 * ∑_{i<N} 4^i`. -/
lemma four_pow_eq (N : ℕ) : 4 ^ N = 1 + 3 * ∑ i ∈ Finset.range N, 4 ^ i := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, pow_succ]; omega

/-- Equation (100): `(4^B - 1)/3 = ∑_{i<B} 4^i`, in the form `3 * y_B + 1 = 4^B`. -/
lemma three_mul_sum_four_pow (B : ℕ) : 3 * ∑ i ∈ Finset.range B, 4 ^ i + 1 = 4 ^ B := by
  have := four_pow_eq B; omega

/-- Equation (21) (Section 2): `3^K 2^M = 2^(M+2K) - ∑_{j=1}^K 3^(j-1) 2^(M+2K-2j)`. -/
theorem recurrence21 (K M : ℕ) :
    (3 : ℤ) ^ K * 2 ^ M = 2 ^ (M + 2 * K) - ∑ j ∈ Icc 1 K, 3 ^ (j - 1) * 2 ^ (M + 2 * K - 2 * j) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have h : ∀ j ∈ Icc 1 K, (3 : ℤ) ^ (j - 1) * 2 ^ (M + 2 * (K + 1) - 2 * j)
          = 4 * ((3 : ℤ) ^ (j - 1) * 2 ^ (M + 2 * K - 2 * j)) := by
        intro j hj
        have hj' := (Finset.mem_Icc.mp hj).2
        have : M + 2 * (K + 1) - 2 * j = (M + 2 * K - 2 * j) + 2 := by omega
        rw [this, pow_add]; ring
      rw [Finset.sum_congr rfl h, ← Finset.mul_sum]
      have e1 : M + 2 * (K + 1) - 2 * (K + 1) = M := by omega
      have e2 : K + 1 - 1 = K := by omega
      rw [e1, e2]
      have e3 : M + 2 * (K + 1) = (M + 2 * K) + 2 := by ring
      rw [e3, pow_add]
      linear_combination 4 * ih

/-- The exponent sequence `(2, 2, …, 2, E, 2, …)`: `p_i = E` at `i = m`, `p_i = 2` elsewhere. -/
def blockSeq (m E : ℕ) (i : ℕ) : ℕ := if i = m then E else 2

lemma Phi_block (m E : ℕ) : Phi (blockSeq m E) m = 3 ^ m * 2 ^ E := by
  rcases m with _ | m
  · simp [Phi_zero, blockSeq]
  · rw [Phi_succ]
    have hc : Phi (blockSeq (m + 1) E) m = Phi (fun _ => 2) m :=
      Phi_congr (fun i hi => by unfold blockSeq; rw [if_neg (by omega)])
    rw [hc, Phi_two]
    have : blockSeq (m + 1) E (m + 1) = E := by simp [blockSeq]
    rw [this]; ring

lemma validExp_block {m E : ℕ} (hm : 1 ≤ m) (hE : 1 ≤ E) : ValidExp (blockSeq m E) := by
  refine ⟨⟨1, le_rfl, ?_⟩, fun i hi => ?_⟩
  · have : (0 : ℕ) ≠ m := by omega
    simp [blockSeq, this]
  · unfold blockSeq; split_ifs <;> omega

lemma tail_succ_zero (p : ℕ → ℕ) (N : ℕ) : tail p (N + 1) 0 = tail p N 0 + p (N + 1) :=
  tail_succ p N 0 (by omega)

lemma tail_zero_zero (p : ℕ → ℕ) : tail p 0 0 = p 0 := by simp [tail]

lemma tail_block_lt (m E : ℕ) : ∀ N, N < m → tail (blockSeq m E) N 0 = 2 * N + 2 := by
  intro N
  induction N with
  | zero =>
      intro h
      rw [tail_zero_zero]; unfold blockSeq; rw [if_neg (by omega)]
  | succ N ih =>
      intro h
      rw [tail_succ_zero, ih (by omega)]; unfold blockSeq; rw [if_neg (by omega)]; omega

/-- `∑_{i=0}^N p_i = 2N + E` for the block sequence (equations (23), (106)). -/
lemma tail_block (m E N : ℕ) (h : m ≤ N) : tail (blockSeq m E) N 0 = 2 * N + E := by
  induction N, h using Nat.le_induction with
  | base =>
      rcases m with _ | m
      · rw [tail_zero_zero]; simp [blockSeq]
      · rw [tail_succ_zero, tail_block_lt (m + 1) E m (by omega)]
        simp [blockSeq]; omega
  | succ N hmN ih =>
      rw [tail_succ_zero, ih]; unfold blockSeq; rw [if_neg (by omega)]; omega

/-- Section 2: the first form `x = 2^M` is included in the fifth form (`n` odd, `n > 2`),
with `p_0 = 2`, `p_i = 2` for `0 < i < (n+1)/2` and `p_((n+1)/2) = M`. -/
theorem first_form_in_fifth {n M : ℕ} (hn : n % 2 = 1) (hn2 : 2 < n) (hM : 1 ≤ M) :
    FifthForm n (2 ^ M) (blockSeq ((n + 1) / 2) M) := by
  have hK : 1 ≤ (n + 1) / 2 := by omega
  refine ⟨hn, by omega, validExp_block hK hM, ?_⟩
  rw [Phi_block]; push_cast <;> ring

/-- Section 4: the second form `x = (2^(2M) - 1)/3` (i.e. `3x+1 = 2^(2M)`) is included in the
fourth form (`m` even). -/
theorem second_form_in_fourth {m M x : ℕ} (hm : m % 2 = 0) (hm2 : 2 ≤ m) (hM : 1 ≤ M)
    (hx : 3 * x + 1 = 2 ^ (2 * M)) : FourthForm m x (blockSeq (m / 2) (2 * M)) := by
  have hK : 1 ≤ m / 2 := by omega
  refine ⟨hm, hm2, validExp_block hK (by omega), ?_⟩
  rw [Phi_block]
  have hxz : (3 : ℤ) * x + 1 = 2 ^ (2 * M) := by exact_mod_cast hx
  linear_combination (3 : ℤ) ^ (m / 2) * hxz

/-- The sequence `p_i = 2` except `p_m = E` and `p_(m+1) = F`. -/
def blockSeq2 (m E F : ℕ) (i : ℕ) : ℕ := if i = m + 1 then F else blockSeq m E i

lemma Phi_block2 (m E F : ℕ) :
    Phi (blockSeq2 m E F) (m + 1) = 2 ^ F * (3 ^ m * 2 ^ E - 3 ^ m) := by
  rw [Phi_succ]
  have hc : Phi (blockSeq2 m E F) m = Phi (blockSeq m E) m :=
    Phi_congr (fun i hi => by unfold blockSeq2; rw [if_neg (by omega)])
  have hF : blockSeq2 m E F (m + 1) = F := by unfold blockSeq2; rw [if_pos rfl]
  rw [hc, hF, Phi_block]

lemma validExp_block2 {m E F : ℕ} (hm : 1 ≤ m) (hE : 1 ≤ E) (hF : 1 ≤ F) :
    ValidExp (blockSeq2 m E F) := by
  refine ⟨⟨1, le_rfl, ?_⟩, fun i hi => ?_⟩
  · have h1 : (0 : ℕ) ≠ m := by omega
    have h2 : (0 : ℕ) ≠ m + 1 := by omega
    simp [blockSeq2, blockSeq, h1, h2]
  · unfold blockSeq2 blockSeq; split_ifs <;> omega

/-- Section 5: the third form `3x = 2^(2M+p₁) - 2^(p₁)` is included in the fifth form
(`L` odd), the last exponent being `p₁`. -/
theorem third_form_in_fifth {L M p1 x : ℕ} (hL : L % 2 = 1) (hL2 : 2 ≤ L) (hM : 1 ≤ M)
    (hp : 1 ≤ p1) (hx : 3 * x + 2 ^ p1 = 2 ^ (2 * M + p1)) :
    FifthForm L x (blockSeq2 ((L + 1) / 2 - 1) (2 * M) p1) := by
  obtain ⟨m, hm⟩ : ∃ m, (L + 1) / 2 = m + 1 := ⟨(L + 1) / 2 - 1, by omega⟩
  have hm1 : 1 ≤ m := by omega
  have hm' : (L + 1) / 2 - 1 = m := by omega
  rw [hm']
  refine ⟨hL, hL2, validExp_block2 hm1 (by omega) hp, ?_⟩
  rw [hm, Phi_block2]
  have hxz : (3 : ℤ) * x + 2 ^ p1 = 2 ^ (2 * M + p1) := by exact_mod_cast hx
  linear_combination (3 : ℤ) ^ m * hxz

/-! ## 7. Section 7: an infinite set of odd numbers with the first final form -/

theorem section7_yB {B N : ℕ} (hB : 1 ≤ B) (hN : 2 ≤ N) :
    FirstFinalForm (∑ i ∈ Finset.range B, 4 ^ i) N (blockSeq N (2 * B)) ∧
    (∑ i ∈ Finset.range B, 4 ^ i) % 2 = 1 ∧
    tail (blockSeq N (2 * B)) N 0 = 2 * B + 2 * N := by
  have h3 := three_mul_sum_four_pow B
  refine ⟨⟨validExp_block (by omega) (by omega), ?_⟩, ?_, ?_⟩
  · rw [Phi_block]
    have hz : ((3 * ∑ i ∈ Finset.range B, 4 ^ i + 1 : ℕ) : ℤ) = ((4 ^ B : ℕ) : ℤ) := by rw [h3]
    push_cast at hz ⊢
    have p1 : (2 : ℤ) ^ (2 * B) = 4 ^ B := pow_four_eq B
    linear_combination (3 : ℤ) ^ N * hz - (3 : ℤ) ^ N * p1
  · have h2 : 2 ∣ 4 ^ B := dvd_pow (by norm_num) (by omega)
    omega
  · rw [tail_block N (2 * B) N le_rfl]; omega

/-- The exponent sequence of the corollaries: `p₀ = 2 + 2D`, `p_m = E`, all other `p_i = 2`. -/
def bumpSeq (D m E : ℕ) (i : ℕ) : ℕ := if i = 0 then 2 + 2 * D else blockSeq m E i

/-- Changing only `p₀` to `p₀ + d` changes `Φ_N` by `(2^d - 1) 2^(∑ p_i)`. -/
lemma Phi_bump (p q : ℕ → ℕ) (d : ℕ) (h0 : q 0 = p 0 + d) (h : ∀ i, 1 ≤ i → q i = p i) :
    ∀ N, Phi q N = Phi p N + ((2 : ℤ) ^ d - 1) * 2 ^ (tail p N 0) := by
  intro N
  induction N with
  | zero => rw [Phi_zero, Phi_zero, h0, tail_zero_zero]; ring
  | succ N ih =>
      rw [Phi_succ, Phi_succ, ih, h (N + 1) (by omega), tail_succ_zero]; ring

lemma Phi_bumpSeq (D m E : ℕ) (hm : 1 ≤ m) :
    Phi (bumpSeq D m E) m = 3 ^ m * 2 ^ E + (4 ^ D - 1) * 2 ^ (2 * m + E) := by
  have h0 : bumpSeq D m E 0 = blockSeq m E 0 + 2 * D := by
    have : (0 : ℕ) ≠ m := by omega
    simp [bumpSeq, blockSeq, this] <;> omega
  have h1 : ∀ i, 1 ≤ i → bumpSeq D m E i = blockSeq m E i := by
    intro i hi; unfold bumpSeq; rw [if_neg (by omega)]
  rw [Phi_bump (blockSeq m E) (bumpSeq D m E) (2 * D) h0 h1 m, Phi_block,
    tail_block m E m le_rfl, pow_four_eq]
  try ring

lemma validExp_bump {D m E : ℕ} (hm : 1 ≤ m) (hE : 1 ≤ E) : ValidExp (bumpSeq D m E) := by
  refine ⟨⟨1 + D, by omega, ?_⟩, fun i hi => ?_⟩
  · simp [bumpSeq]; ring
  · unfold bumpSeq; rw [if_neg (by omega)]; exact (validExp_block hm hE).2 i hi

/-- Equations (107)–(118), first corollary: if `4^D = 3^(N+1) E + 1` then
`y_C = E 2^(2B+2N) + ∑_{i<B} 4^i` has the first final form with `p₀ = 2 + 2D`. -/
theorem corollary1 {B N D E : ℕ} (hB : 1 ≤ B) (hN : 2 ≤ N)
    (hE : 4 ^ D = 3 ^ (N + 1) * E + 1) :
    FirstFinalForm (E * 2 ^ (2 * B + 2 * N) + ∑ i ∈ Finset.range B, 4 ^ i) N
      (bumpSeq D N (2 * B)) := by
  refine ⟨validExp_bump (by omega) (by omega), ?_⟩
  rw [Phi_bumpSeq D N (2 * B) (by omega)]
  have h3 := three_mul_sum_four_pow B
  have hz : ((3 * ∑ i ∈ Finset.range B, 4 ^ i + 1 : ℕ) : ℤ) = ((4 ^ B : ℕ) : ℤ) := by rw [h3]
  have hEz : ((4 ^ D : ℕ) : ℤ) = ((3 ^ (N + 1) * E + 1 : ℕ) : ℤ) := by rw [hE]
  push_cast at hz hEz ⊢
  have p1 : (2 : ℤ) ^ (2 * B) = 4 ^ B := pow_four_eq B
  linear_combination (3 : ℤ) ^ N * hz - (3 : ℤ) ^ N * p1 - (2 : ℤ) ^ (2 * N + 2 * B) * hEz

lemma not_pow_of_odd {B w M : ℕ} (hw : w % 2 = 1) (hw1 : w ≠ 1) :
    4 ^ B * w ≠ 2 ^ (2 * M) := by
  intro h
  rw [four_pow_eq_two_pow] at h
  have h' : 2 ^ (2 * B) * w = 2 ^ (2 * M) * 1 := by rw [mul_one]; exact h
  have := two_pow_mul_odd_inj hw (by norm_num : 1 % 2 = 1) h'
  exact hw1 this.2

/-- The explicit example `N = 2`, `E = 9709`, `D = 9` of equation (114). -/
theorem corollary1_concrete (B : ℕ) (hB : 1 ≤ B) :
    FirstFinalForm (155343 * 4 ^ B + ∑ i ∈ Finset.range (B + 1), 4 ^ i) 2 (bumpSeq 9 2 (2 * B)) := by
  have h := corollary1 (B := B) (N := 2) (D := 9) (E := 9709) hB le_rfl (by norm_num)
  have e : 9709 * 2 ^ (2 * B + 2 * 2) + ∑ i ∈ Finset.range B, 4 ^ i
      = 155343 * 4 ^ B + ∑ i ∈ Finset.range (B + 1), 4 ^ i := by
    rw [Finset.sum_range_succ]
    have : 2 ^ (2 * B + 2 * 2) = 16 * 4 ^ B := by
      rw [pow_add, ← four_pow_eq_two_pow]; norm_num; ring
    rw [this]; omega
  rw [e] at h; exact h

/-- Equation (119): `y_C` is never of the second form. -/
theorem corollary1_not_second_form (B : ℕ) :
    ¬ ∃ M, 3 * (155343 * 4 ^ B + ∑ i ∈ Finset.range (B + 1), 4 ^ i) + 1 = 2 ^ (2 * M) := by
  rintro ⟨M, hM⟩
  have h3 := three_mul_sum_four_pow B
  rw [Finset.sum_range_succ] at hM
  have : 3 * (155343 * 4 ^ B + (∑ i ∈ Finset.range B, 4 ^ i + 4 ^ B)) + 1 = 4 ^ B * 466033 := by
    omega
  rw [this] at hM
  exact not_pow_of_odd (by norm_num) (by norm_num) hM

/-- Equations (127)–(131): `E = (4^(3^N) - 1)/3^(N+1)` is a natural number.
(The article obtains this from the Fermat–Euler theorem; here it is proved directly by
induction on `N`, using `a³ - 1 = (a - 1)(a² + a + 1)`.) -/
theorem fermat_euler_E (N : ℕ) : ∃ E, 1 ≤ E ∧ 4 ^ (3 ^ N) = 3 ^ (N + 1) * E + 1 := by
  induction N with
  | zero => exact ⟨1, le_rfl, by norm_num⟩
  | succ N ih =>
      obtain ⟨E, hE1, hE⟩ := ih
      refine ⟨E + 3 ^ (N + 1) * E ^ 2 + 3 ^ (2 * N + 1) * E ^ 3, by omega, ?_⟩
      have : 4 ^ (3 ^ (N + 1)) = (4 ^ (3 ^ N)) ^ 3 := by rw [pow_succ, pow_mul]
      rw [this, hE]; ring

/-- Second corollary (equations (121)–(141)): for each `N ≥ 2`, `D = 3^N`. -/
theorem corollary2 {B N : ℕ} (hB : 1 ≤ B) (hN : 2 ≤ N) :
    ∃ E, 1 ≤ E ∧ 4 ^ (3 ^ N) = 3 ^ (N + 1) * E + 1 ∧
      FirstFinalForm (E * 2 ^ (2 * B + 2 * N) + ∑ i ∈ Finset.range B, 4 ^ i) N
        (bumpSeq (3 ^ N) N (2 * B)) ∧
      ¬ ∃ M, 3 * (E * 2 ^ (2 * B + 2 * N) + ∑ i ∈ Finset.range B, 4 ^ i) + 1 = 2 ^ (2 * M) := by
  obtain ⟨E, hE1, hE⟩ := fermat_euler_E N
  refine ⟨E, hE1, hE, corollary1 hB hN hE, ?_⟩
  rintro ⟨M, hM⟩
  have h3 := three_mul_sum_four_pow B
  have h4 : 2 ^ (2 * B + 2 * N) = 4 ^ B * 4 ^ N := by
    rw [pow_add, ← four_pow_eq_two_pow, ← four_pow_eq_two_pow]
  have hw : 3 * (E * 2 ^ (2 * B + 2 * N) + ∑ i ∈ Finset.range B, 4 ^ i) + 1
      = 4 ^ B * (3 * (E * 4 ^ N) + 1) := by
    have hz : ((3 * ∑ i ∈ Finset.range B, 4 ^ i + 1 : ℕ) : ℤ) = ((4 ^ B : ℕ) : ℤ) := by rw [h3]
    rw [h4]
    have : (3 * (E * (4 ^ B * 4 ^ N) + ∑ i ∈ Finset.range B, 4 ^ i) + 1 : ℤ)
        = 4 ^ B * (3 * (E * 4 ^ N) + 1) := by
      push_cast at hz; linear_combination hz
    exact_mod_cast this
  rw [hw] at hM
  have h2 : 2 ∣ 4 ^ N := dvd_pow (by norm_num) (by omega)
  obtain ⟨c, hc⟩ := h2
  have hpos : 1 ≤ E * 4 ^ N := Nat.mul_pos (by omega) (by positivity)
  refine not_pow_of_odd (B := B) (w := 3 * (E * 4 ^ N) + 1) (M := M) ?_ ?_ hM
  · have : E * 4 ^ N = 2 * (E * c) := by rw [hc]; ring
    omega
  · omega


/-! ## 8. Appendix: a sequence related to the second form -/

/-- `V_n = 0` if `n` is even, `V_n = 1` if `n` is odd. -/
def Vseq (n : ℕ) : ℤ := if n % 2 = 0 then 0 else 1

/-- The constant term in (178)/(179): `2^(n+2)` for `n` even, `2^(n+1)` for `n` odd. -/
def cseq (n : ℕ) : ℤ := if n % 2 = 0 then 2 ^ (n + 2) else 2 ^ (n + 1)

/-- Equations (178), (179): from `3 k₀ = 2^(p-1) - 2` and `2 k_(n+1) = k_n - V_n` we get
`2^p = 3 · 2^(n+1) · k_n + c_n`. -/
theorem appendix_invariant (p : ℕ) (hp : 1 ≤ p) (k : ℕ → ℤ) (h0 : 3 * k 0 = 2 ^ (p - 1) - 2) :
    ∀ n, (∀ m, m < n → 2 * k (m + 1) = k m - Vseq m) →
      (2 : ℤ) ^ p = 3 * 2 ^ (n + 1) * k n + cseq n := by
  intro n
  induction n with
  | zero =>
      intro _
      have e : (2 : ℤ) ^ p = 2 * 2 ^ (p - 1) := by
        rw [← pow_succ']; congr 1; omega
      have hc : cseq 0 = 4 := by simp [cseq]
      rw [hc]
      linear_combination e - 2 * h0
  | succ n ih =>
      intro hs
      have ih' := ih (fun m hm => hs m (by omega))
      have hn := hs n (by omega)
      rcases Nat.mod_two_eq_zero_or_one n with h | h
      · have hn1 : (n + 1) % 2 = 1 := by omega
        have e1 : Vseq n = 0 := by simp [Vseq, h]
        have e2 : cseq n = 2 ^ (n + 2) := by simp [cseq, h]
        have e3 : cseq (n + 1) = 2 ^ (n + 2) := by
          unfold cseq; split_ifs <;> first | omega | ring
        rw [e1] at hn; rw [e2] at ih'; rw [e3]
        linear_combination ih' - 3 * 2 ^ (n + 1) * hn
      · have hn1 : (n + 1) % 2 = 0 := by omega
        have e1 : Vseq n = 1 := by simp [Vseq, h]
        have e2 : cseq n = 2 ^ (n + 1) := by simp [cseq, h]
        have e3 : cseq (n + 1) = 2 ^ (n + 3) := by
          unfold cseq; split_ifs <;> first | omega | ring
        rw [e1] at hn; rw [e2] at ih'; rw [e3]
        linear_combination ih' - 3 * 2 ^ (n + 1) * hn

/-- `x = 2 k₀ + 1` satisfies `3x + 1 = 2^p` (equations (172)–(173)). -/
theorem appendix_x (p : ℕ) (hp : 1 ≤ p) (k : ℕ → ℤ) (h0 : 3 * k 0 = 2 ^ (p - 1) - 2) :
    3 * (2 * k 0 + 1) + 1 = (2 : ℤ) ^ p := by
  have e : (2 : ℤ) ^ p = 2 * 2 ^ (p - 1) := by
    rw [← pow_succ']; congr 1; omega
  linear_combination 2 * h0 - e

/-- If the sequence ends with `k_(p-1) = 0`, then `p` is even. -/
theorem appendix_p_even (p : ℕ) (hp : 1 ≤ p) (k : ℕ → ℤ) (h0 : 3 * k 0 = 2 ^ (p - 1) - 2)
    (hs : ∀ m, m < p - 1 → 2 * k (m + 1) = k m - Vseq m) (hlast : k (p - 1) = 0) :
    p % 2 = 0 := by
  have h := appendix_invariant p hp k h0 (p - 1) hs
  rw [hlast] at h
  by_contra hodd
  have hev : (p - 1) % 2 = 0 := by omega
  have hc : cseq (p - 1) = 2 ^ (p - 1 + 2) := by simp [cseq, hev]
  rw [hc] at h
  have e : (2 : ℤ) ^ (p - 1 + 2) = 2 * 2 ^ p := by
    rw [show p - 1 + 2 = p + 1 by omega]; ring
  have hpos : (0 : ℤ) < 2 ^ p := by positivity
  simp only [mul_zero, zero_add] at h
  linarith

lemma pow_two_mod_three_aux (e : ℕ) : (2 : ℤ) ^ e % 3 = if e % 2 = 0 then 1 else 2 := by
  induction e with
  | zero => norm_num
  | succ e ih =>
      rw [pow_succ]
      split_ifs at ih ⊢ <;> omega

/-- Equations (182)–(185): `2^p ≡ (-1)^p (mod 3)`. -/
theorem two_pow_modEq_neg_one_pow (p : ℕ) : (2 : ℤ) ^ p ≡ (-1) ^ p [ZMOD 3] := by
  have h : (2 : ℤ) ≡ -1 [ZMOD 3] := by decide
  exact h.pow p

/-- Equation (184)–(185): if `3 x' = 2^p - 1`, then `p` is even. -/
theorem appendix_mod_three {p x : ℕ} (h : 3 * x + 1 = 2 ^ p) : p % 2 = 0 := by
  have hz : (3 : ℤ) * x + 1 = 2 ^ p := by exact_mod_cast h
  have hm := pow_two_mod_three_aux p
  by_contra hodd
  rw [if_neg hodd] at hm
  omega

/-- The explicit sequence of the appendix, defined from the end (`k_(p-1) = 0`) by closed form
`k_n = (2^(p-1-n) - (2 if n even, 1 if n odd)) / 3`. -/
def kseq (p n : ℕ) : ℤ := ((2 : ℤ) ^ (p - 1 - n) - (if n % 2 = 0 then 2 else 1)) / 3

lemma kseq_spec {p n : ℕ} (hp : p % 2 = 0) (hp2 : 2 ≤ p) (hn : n ≤ p - 1) :
    3 * kseq p n = 2 ^ (p - 1 - n) - (if n % 2 = 0 then 2 else 1) := by
  unfold kseq
  have hm := pow_two_mod_three_aux (p - 1 - n)
  by_cases h : n % 2 = 0
  · have h1 : ¬ (p - 1 - n) % 2 = 0 := by omega
    rw [if_neg h1] at hm
    rw [if_pos h]
    omega
  · have h1 : (p - 1 - n) % 2 = 0 := by omega
    rw [if_pos h1] at hm
    rw [if_neg h]
    omega

/-- The sequence `kseq p` satisfies `3 k₀ = 2^(p-1) - 2`, `2 k_(n+1) = k_n - V_n` for
`n < p - 1`, and `k_(p-1) = 0` (for every even `p ≥ 2`). -/
theorem kseq_properties {p : ℕ} (hp : p % 2 = 0) (hp2 : 2 ≤ p) :
    3 * kseq p 0 = 2 ^ (p - 1) - 2 ∧
    (∀ m, m < p - 1 → 2 * kseq p (m + 1) = kseq p m - Vseq m) ∧ kseq p (p - 1) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · have := kseq_spec (n := 0) hp hp2 (by omega)
    simpa using this
  · intro m hm
    have s1 := kseq_spec (n := m) hp hp2 (by omega)
    have s2 := kseq_spec (n := m + 1) hp hp2 (by omega)
    have pw : (2 : ℤ) ^ (p - 1 - m) = 2 * 2 ^ (p - 1 - (m + 1)) := by
      rw [← pow_succ']; congr 1; omega
    unfold Vseq
    rcases Nat.mod_two_eq_zero_or_one m with h | h
    · have h' : ¬ (m + 1) % 2 = 0 := by omega
      rw [if_pos h] at s1 ⊢
      rw [if_neg h'] at s2
      omega
    · have h0 : ¬ m % 2 = 0 := by omega
      have h' : (m + 1) % 2 = 0 := by omega
      rw [if_neg h0] at s1 ⊢
      rw [if_pos h'] at s2
      omega
  · have s := kseq_spec (n := p - 1) hp hp2 le_rfl
    have h0 : ¬ (p - 1) % 2 = 0 := by omega
    rw [if_neg h0] at s
    simp at s
    omega

/-- The method of the appendix: for each even `p ≥ 2`, the number `x = 2 k₀ + 1` computed
by the sequence satisfies `3x + 1 = 2^p`. -/
theorem appendix_method {p : ℕ} (hp : p % 2 = 0) (hp2 : 2 ≤ p) :
    3 * (2 * kseq p 0 + 1) + 1 = (2 : ℤ) ^ p :=
  appendix_x p (by omega) (kseq p) (kseq_properties hp hp2).1

/-- The example `p = 4`: `k₃ = 0 ⇒ k₂ = 0 ⇒ k₁ = 1 ⇒ k₀ = 2`, `x = 5`, `3x + 1 = 16`
(equations (180)–(181)). -/
theorem appendix_example :
    kseq 4 3 = 0 ∧ kseq 4 2 = 0 ∧ kseq 4 1 = 1 ∧ kseq 4 0 = 2 ∧
    2 * kseq 4 0 + 1 = 5 ∧ 3 * 5 + 1 = 2 ^ 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, by norm_num⟩ <;> norm_num [kseq]


/-! ## 9. Section 8: the numbers `4B + 1` and `4B - 1`

Throughout, `p` is an exponent sequence of a first final form of `4B + 1` and `q` one of
`4B - 1`, both with the same `N = K + 2` (which is possible by Section 3). -/

/-- Equation (144). -/
lemma eq144 (B : ℕ) (hB : 1 ≤ B) :
    4 * B + 1 = 2 * (2 * B) + 1 ∧ 4 * B - 1 = 2 * (2 * B - 1) + 1 := by omega

/-- Equations (146) and (147). -/
lemma eq146_147 (B N : ℕ) (hB : 1 ≤ B) :
    (3 : ℤ) ^ (N + 1) * ((4 * B - 1 : ℕ) : ℤ) + 3 ^ N = 3 ^ N * (12 * B - 2) ∧
    (3 : ℤ) ^ (N + 1) * ((4 * B - 1 : ℕ) : ℤ) + 3 ^ N = 3 ^ N * (12 * B + 4) - 2 * 3 ^ (N + 1) ∧
    (3 : ℤ) ^ (N + 1) * ((4 * B + 1 : ℕ) : ℤ) + 3 ^ N
      = ((3 : ℤ) ^ (N + 1) * ((4 * B - 1 : ℕ) : ℤ) + 3 ^ N) + 2 * 3 ^ (N + 1) := by
  have hc : ((4 * B - 1 : ℕ) : ℤ) = 4 * B - 1 := by
    have : 1 ≤ 4 * B := by omega
    push_cast [Nat.cast_sub this]; ring
  rw [hc]
  push_cast
  refine ⟨by ring, by ring, by ring⟩

/-- Equation (142)-(143) consequences: the last two exponents of the form of `4B - 1`.
`q_N = 1` (because `3^(N+1)(4B-1) + 3^N` is divisible by `2` but not by `4`), and
`2^(q_(N-1)) · z = 2 (9B - 1)` with `z` odd. -/
lemma s8_q {B K : ℕ} {q : ℕ → ℕ} (hB : 1 ≤ B) (hq : FirstFinalForm (4 * B - 1) (K + 1 + 1) q) :
    q (K + 1 + 1) = 1 ∧ ∃ z, z % 2 = 1 ∧ 2 ^ (q (K + 1)) * z = 2 * (9 * B - 1) := by
  obtain ⟨y1, hy1, hodd1, hf1⟩ := peel hq
  have h6 : 2 ^ (q (K + 1 + 1)) * y1 = 2 ^ 1 * (6 * B - 1) := by rw [← hy1]; omega
  obtain ⟨he, hyy⟩ := two_pow_mul_odd_inj hodd1 (by omega) h6
  obtain ⟨y2, hy2, hodd2, hf2⟩ := peel hf1
  refine ⟨by omega, y2, hodd2, ?_⟩
  rw [← hy2, hyy]; omega

/-- Equation (151): if `q_(N-1) ≥ 4` then `p_N = 4`. -/
lemma s8_pN_four {B K : ℕ} {p q : ℕ → ℕ} (hB : 1 ≤ B)
    (hp : FirstFinalForm (4 * B + 1) (K + 1 + 1) p)
    (hq : FirstFinalForm (4 * B - 1) (K + 1 + 1) q) (h4 : 4 ≤ q (K + 1)) :
    p (K + 1 + 1) = 4 := by
  obtain ⟨_, z, hz, hzeq⟩ := s8_q hB hq
  obtain ⟨r, hr⟩ : ∃ r, q (K + 1) = 4 + r := ⟨q (K + 1) - 4, by omega⟩
  rw [hr, pow_add] at hzeq
  have hmul : 2 ^ 4 * 2 ^ r * z = 16 * (2 ^ r * z) := by ring
  have hmod : B % 8 = 1 := by omega
  obtain ⟨y1, hy1, hodd1, _⟩ := peel hp
  have hw : ((3 * B + 1) / 4) % 2 = 1 := by omega
  have h16 : 3 * (4 * B + 1) + 1 = 2 ^ 4 * ((3 * B + 1) / 4) := by omega
  exact (two_pow_mul_odd_inj hodd1 hw (hy1.symm.trans h16)).1

/-- Equation (154): if `q_(N-1) > 4` then `p_(N-1) = 1`. -/
lemma s8_pN1_one {B K : ℕ} {p q : ℕ → ℕ} (hB : 1 ≤ B)
    (hp : FirstFinalForm (4 * B + 1) (K + 1 + 1) p)
    (hq : FirstFinalForm (4 * B - 1) (K + 1 + 1) q) (h5 : 5 ≤ q (K + 1)) :
    p (K + 1) = 1 := by
  obtain ⟨_, z, hz, hzeq⟩ := s8_q hB hq
  obtain ⟨r, hr⟩ : ∃ r, q (K + 1) = 5 + r := ⟨q (K + 1) - 5, by omega⟩
  rw [hr, pow_add] at hzeq
  have hmul : 2 ^ 5 * 2 ^ r * z = 32 * (2 ^ r * z) := by ring
  have hmod : B % 16 = 9 := by omega
  obtain ⟨y1, hy1, hodd1, hf1⟩ := peel hp
  have hw : ((3 * B + 1) / 4) % 2 = 1 := by omega
  have h16 : 3 * (4 * B + 1) + 1 = 2 ^ 4 * ((3 * B + 1) / 4) := by omega
  obtain ⟨_, hyy⟩ := two_pow_mul_odd_inj hodd1 hw (hy1.symm.trans h16)
  obtain ⟨y2, hy2, hodd2, _⟩ := peel hf1
  have hv : ((3 * ((3 * B + 1) / 4) + 1) / 2) % 2 = 1 := by omega
  have h2 : 3 * y1 + 1 = 2 ^ 1 * ((3 * ((3 * B + 1) / 4) + 1) / 2) := by omega
  exact (two_pow_mul_odd_inj hodd2 hv (hy2.symm.trans h2)).1

/-- Equation (156): `q_(N-1) = 6` forces `p_N = 4` and `p_(N-1) = 1`. -/
lemma s8_156 {B K : ℕ} {p q : ℕ → ℕ} (hB : 1 ≤ B)
    (hp : FirstFinalForm (4 * B + 1) (K + 1 + 1) p)
    (hq : FirstFinalForm (4 * B - 1) (K + 1 + 1) q) (h6 : q (K + 1) = 6) :
    p (K + 1 + 1) = 4 ∧ p (K + 1) = 1 :=
  ⟨s8_pN_four hB hp hq (by omega), s8_pN1_one hB hp hq (by omega)⟩

/-- The statement (161) of Section 8.3, as formulated in Section 8.1/8.2 of the article
(equation (156), last clause): when `q_(N-1) = 6`, the exponents `p_i` and `q_i` agree for
`0 ≤ i ≤ N - 2`. -/
def Article161 : Prop :=
  ∀ (B N : ℕ) (p q : ℕ → ℕ), 1 ≤ B → 3 ≤ N →
    FirstFinalForm (4 * B + 1) N p → FirstFinalForm (4 * B - 1) N q →
    q (N - 1) = 6 → ∀ i, i ≤ N - 2 → p i = q i

/-- Equations (157)–(165): with `q_(N-1) = 6`, `p_N = 4`, `p_(N-1) = 1`, `q_N = 1` and
`p_i = q_i` for `i ≤ N - 2`, a contradiction is obtained. -/
theorem s8_core {B K : ℕ} {p q : ℕ → ℕ} (hB : 1 ≤ B)
    (hp : FirstFinalForm (4 * B + 1) (K + 1 + 1) p)
    (hq : FirstFinalForm (4 * B - 1) (K + 1 + 1) q)
    (h6 : q (K + 1) = 6) (h161 : ∀ i, i ≤ K → p i = q i) : False := by
  obtain ⟨hqN, z, hz, hzeq⟩ := s8_q hB hq
  obtain ⟨hp2, hp1⟩ := s8_156 hB hp hq h6
  have ep := hp.2
  have eq := hq.2
  have hc : ((4 * B - 1 : ℕ) : ℤ) = 4 * B - 1 := by
    have : 1 ≤ 4 * B := by omega
    push_cast [Nat.cast_sub this]; ring
  rw [hc] at eq
  rw [Phi_succ, Phi_succ, hp2, hp1] at ep
  rw [Phi_succ, Phi_succ, hqN, h6] at eq
  have hΦ : Phi p K = Phi q K := Phi_congr h161
  rw [hΦ] at ep
  push_cast at ep eq
  have ht : (0 : ℤ) < 3 ^ K := by positivity
  have hb : (0 : ℤ) < B := by exact_mod_cast hB
  have key : 324 * ((3 : ℤ) ^ K * B) + 348 * 3 ^ K = 0 := by
    linear_combination 4 * ep - eq
  nlinarith [mul_pos ht hb]

/-- Equation (166): under the statement (161), `q_(N-1) ≠ 6`. -/
theorem section8_166 (h : Article161) {B N : ℕ} {p q : ℕ → ℕ} (hB : 1 ≤ B) (hN : 3 ≤ N)
    (hp : FirstFinalForm (4 * B + 1) N p) (hq : FirstFinalForm (4 * B - 1) N q) :
    q (N - 1) ≠ 6 := by
  intro h6
  obtain ⟨K, rfl⟩ : ∃ K, N = K + 1 + 1 := ⟨N - 2, by omega⟩
  have h6' : q (K + 1) = 6 := by simpa using h6
  exact s8_core hB hp hq h6' (fun i hi => h B (K + 1 + 1) p q hB hN hp hq h6 i (by omega))

/-- Equation (170): for `B = 25`, `(9B - 1)/2^5 = 7`, and `7 = 4·2 - 1`. -/
theorem section8_seven : (9 * 25 - 1) / 2 ^ 5 = 7 ∧ (7 : ℕ) = 4 * 2 - 1 := by norm_num

/-- Section 8, conclusion: from the statement (161) it follows that the Collatz conjecture
(every odd number, in particular `4B + 1` and `4B - 1` with `B = 25`, having a first final form)
cannot hold. -/
theorem section8_conclusion (h : Article161) : ¬ CollatzConjecture := by
  intro hC
  obtain ⟨N1, p, hp1⟩ := (odd_reachesOne_iff_form (x := 4 * 25 + 1) (by norm_num)).mp
    (hC _ (by norm_num))
  obtain ⟨N2, q, hq1⟩ := (odd_reachesOne_iff_form (x := 4 * 25 - 1) (by norm_num)).mp
    (hC _ (by norm_num))
  have hp' := form_shift hp1 (N2 + 3)
  have hq' := form_shift hq1 (N1 + 3)
  obtain ⟨K, hK⟩ : ∃ K, N1 + (N2 + 3) = K + 1 + 1 := ⟨N1 + N2 + 1, by omega⟩
  have hK' : N2 + (N1 + 3) = K + 1 + 1 := by omega
  rw [hK] at hp'
  rw [hK'] at hq'
  obtain ⟨_, z, hz, hzeq⟩ := s8_q (B := 25) (by norm_num) hq'
  have h448 : 2 ^ (shiftSeq q (N1 + 3) (K + 1)) * z = 2 ^ 6 * 7 := by
    rw [hzeq]; norm_num
  have h6 : shiftSeq q (N1 + 3) (K + 1) = 6 :=
    (two_pow_mul_odd_inj hz (by norm_num) h448).1
  exact section8_166 h (B := 25) (by norm_num) (by omega) hp' hq' (by simpa using h6)

end LouizCollatz
