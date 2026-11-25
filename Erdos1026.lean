/-
Copyright 2026 laughingbear. Released under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# Erdős Problem 1026: every constant `c ≤ 1` is admissible

Standalone proof of `erdos_1026.variants.lower_bound` from google-deepmind/formal-conjectures
(`FormalConjectures/ErdosProblems/1026.lean`). The definitions `monotonicSubsequenceSums` and
`admissibleConstants` are copied verbatim, and the statement is byte-identical to the original.

The proof shows more: every sequence of `n ≥ 1` distinct positive reals has a monotone
subsequence with sum at least `(∑ xᵢ) / √n` (`exists_monotone_sum_ge`), so every `c ≤ 1` is
admissible (`mem_admissibleConstants_of_le_one`).

Proof (weighted Erdős–Szekeres): let `A i` and `D i` be the largest sums of an increasing and a
decreasing subsequence ending at `i`. For `i < j`, `A j ≥ A i + x j` if `x i < x j`, and
`D j ≥ D i + x j` otherwise. So the squares `(A i - x i, A i] × (D i - x i, D i]` are pairwise
disjoint and lie in `(0, M] × (0, M]`, where `M` is the largest monotone sum. Comparing areas gives
`∑ xᵢ² ≤ M²`, and Cauchy–Schwarz gives `(∑ xᵢ)² ≤ n ∑ xᵢ²`.
-/

open Finset MeasureTheory Filter

namespace Erdos1026

/--
The set of sums $\sum x_{i_r}$, where $x_{i_1},\ldots,x_{i_r}$ ranges over the monotonic
subsequences of the sequence $x_1,\ldots,x_n$.
-/
def monotonicSubsequenceSums {n : ℕ} (x : Fin n → ℝ) : Set ℝ :=
  {S | ∃ I : Finset (Fin n), (MonotoneOn x ↑I ∨ AntitoneOn x ↑I) ∧ (∑ i ∈ I, x i) = S}

/--
The set of constants $c$ such that, for all sequences of $n$ distinct positive real numbers
$x_1,\ldots,x_n$,
$$
\max\left(\sum x_{i_r}\right) > (c-o(1))\frac{1}{\sqrt{n}}\sum x_i
$$
(where the maximum is taken over all monotonic subsequences).

The source reduces to positive sequences. With signed sequences the condition is not a vanishing
error term: for $\varepsilon > |c|$ and $x_i = -i$ the right-hand side is positive while every
subsequence sum is nonpositive, so no constant would be admissible.
-/
def admissibleConstants : Set ℝ :=
  {c : ℝ | ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ x : Fin n → ℝ, Function.Injective x →
    (∀ i, 0 < x i) →
    ∃ S ∈ monotonicSubsequenceSums x, (c - ε) / Real.sqrt (n : ℝ) * (∑ i, x i) ≤ S}

section Square

variable {n : ℕ} (x : Fin n → ℝ)

open scoped Classical in
/-- Index sets of increasing subsequences that end at `i`. -/
noncomputable def incCands (i : Fin n) : Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Finset (Fin n))).filter
    fun I => i ∈ I ∧ (∀ j ∈ I, j ≤ i) ∧ MonotoneOn x (I : Set (Fin n))

open scoped Classical in
/-- Index sets of decreasing subsequences that end at `i`. -/
noncomputable def decCands (i : Fin n) : Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Finset (Fin n))).filter
    fun I => i ∈ I ∧ (∀ j ∈ I, j ≤ i) ∧ AntitoneOn x (I : Set (Fin n))

lemma singleton_mem_incCands (i : Fin n) : {i} ∈ incCands x i := by
  classical
  simp [incCands, MonotoneOn]

lemma singleton_mem_decCands (i : Fin n) : {i} ∈ decCands x i := by
  classical
  simp [decCands, AntitoneOn]

lemma incCands_nonempty (i : Fin n) : (incCands x i).Nonempty := ⟨_, singleton_mem_incCands x i⟩

lemma decCands_nonempty (i : Fin n) : (decCands x i).Nonempty := ⟨_, singleton_mem_decCands x i⟩

/-- Largest sum of an increasing subsequence ending at `i`. -/
noncomputable def A (i : Fin n) : ℝ := (incCands x i).sup' (incCands_nonempty x i) fun I => ∑ j ∈ I, x j

/-- Largest sum of a decreasing subsequence ending at `i`. -/
noncomputable def D (i : Fin n) : ℝ := (decCands x i).sup' (decCands_nonempty x i) fun I => ∑ j ∈ I, x j

lemma le_A (i : Fin n) : x i ≤ A x i := by
  have h := Finset.le_sup' (fun I => ∑ j ∈ I, x j) (singleton_mem_incCands x i)
  rw [Finset.sum_singleton] at h
  exact h

lemma le_D (i : Fin n) : x i ≤ D x i := by
  have h := Finset.le_sup' (fun I => ∑ j ∈ I, x j) (singleton_mem_decCands x i)
  rw [Finset.sum_singleton] at h
  exact h

lemma A_add_le {i j : Fin n} (hij : i < j) (hx : x i < x j) : A x i + x j ≤ A x j := by
  classical
  obtain ⟨I, hI, hIeq⟩ := Finset.exists_mem_eq_sup' (incCands_nonempty x i) fun I => ∑ k ∈ I, x k
  rw [incCands, Finset.mem_filter] at hI
  obtain ⟨-, hiI, hle, hmono⟩ := hI
  have hjI : j ∉ I := fun h => absurd (hle j h) (not_le.mpr hij)
  have hmem : insert j I ∈ incCands x j := by
    rw [incCands, Finset.mem_filter, Finset.coe_insert]
    refine ⟨Finset.mem_univ _, Finset.mem_insert_self _ _, ?_, ?_⟩
    · intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact le_rfl
      · exact (hle k hk).trans hij.le
    · intro a ha b hb hab
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact le_rfl
      · exact absurd ((hle b hb).trans_lt hij) (not_lt.mpr hab)
      · exact (hmono ha hiI (hle a ha)).trans hx.le
      · exact hmono ha hb hab
  have hS : ∑ k ∈ insert j I, x k = x j + (A x i) := by
    rw [Finset.sum_insert hjI]
    exact congrArg (x j + ·) hIeq.symm
  calc A x i + x j = ∑ k ∈ insert j I, x k := by rw [hS, add_comm]
    _ ≤ _ := Finset.le_sup' (fun I => ∑ k ∈ I, x k) hmem

lemma D_add_le {i j : Fin n} (hij : i < j) (hx : x j < x i) : D x i + x j ≤ D x j := by
  classical
  obtain ⟨I, hI, hIeq⟩ := Finset.exists_mem_eq_sup' (decCands_nonempty x i) fun I => ∑ k ∈ I, x k
  rw [decCands, Finset.mem_filter] at hI
  obtain ⟨-, hiI, hle, hmono⟩ := hI
  have hjI : j ∉ I := fun h => absurd (hle j h) (not_le.mpr hij)
  have hmem : insert j I ∈ decCands x j := by
    rw [decCands, Finset.mem_filter, Finset.coe_insert]
    refine ⟨Finset.mem_univ _, Finset.mem_insert_self _ _, ?_, ?_⟩
    · intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact le_rfl
      · exact (hle k hk).trans hij.le
    · intro a ha b hb hab
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact le_rfl
      · exact absurd ((hle b hb).trans_lt hij) (not_lt.mpr hab)
      · exact hx.le.trans (hmono ha hiI (hle a ha))
      · exact hmono ha hb hab
  have hS : ∑ k ∈ insert j I, x k = x j + (D x i) := by
    rw [Finset.sum_insert hjI]
    exact congrArg (x j + ·) hIeq.symm
  calc D x i + x j = ∑ k ∈ insert j I, x k := by rw [hS, add_comm]
    _ ≤ _ := Finset.le_sup' (fun I => ∑ k ∈ I, x k) hmem

lemma A_mem (i : Fin n) : A x i ∈ monotonicSubsequenceSums x := by
  classical
  obtain ⟨I, hI, hIeq⟩ := Finset.exists_mem_eq_sup' (incCands_nonempty x i) fun I => ∑ k ∈ I, x k
  simp only [incCands, Finset.mem_filter, Finset.mem_univ, true_and] at hI
  exact ⟨I, Or.inl hI.2.2, hIeq.symm⟩

lemma D_mem (i : Fin n) : D x i ∈ monotonicSubsequenceSums x := by
  classical
  obtain ⟨I, hI, hIeq⟩ := Finset.exists_mem_eq_sup' (decCands_nonempty x i) fun I => ∑ k ∈ I, x k
  simp only [decCands, Finset.mem_filter, Finset.mem_univ, true_and] at hI
  exact ⟨I, Or.inr hI.2.2, hIeq.symm⟩

/-- The square attached to the `i`-th term. -/
def square (i : Fin n) : Set (ℝ × ℝ) :=
  Set.Ioc (A x i - x i) (A x i) ×ˢ Set.Ioc (D x i - x i) (D x i)

lemma square_disjoint (hinj : Function.Injective x) {i j : Fin n} (hij : i < j) :
    Disjoint (square x i) (square x j) := by
  rw [Set.disjoint_left]
  rintro ⟨p, q⟩ ⟨⟨hp1, hp2⟩, hq1, hq2⟩ ⟨⟨hp1', hp2'⟩, hq1', hq2'⟩
  rcases lt_or_gt_of_ne (hinj.ne hij.ne) with h | h
  · have := A_add_le x hij h
    linarith
  · have := D_add_le x hij h
    linarith

/-- Weighted Erdős–Szekeres: the squares are disjoint and fit in `(0, M] × (0, M]`. -/
lemma sum_sq_le (hinj : Function.Injective x) (M : ℝ) (hM : ∀ i, A x i ≤ M ∧ D x i ≤ M)
    (hpos : ∀ i, 0 < x i) : ∑ i, x i ^ 2 ≤ M ^ 2 := by
  classical
  have hM0 : ∀ i, 0 ≤ M := fun i => (hpos i).le.trans ((le_A x i).trans (hM i).1)
  by_cases hn : n = 0
  · subst hn; simp; positivity
  have hM0' : 0 ≤ M := hM0 ⟨0, Nat.pos_of_ne_zero hn⟩
  have hdisj : (Set.univ : Set (Fin n)).PairwiseDisjoint (square x) := by
    intro i _ j _ hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact square_disjoint x hinj h
    · exact (square_disjoint x hinj h).symm
  have hsub : (⋃ i ∈ (Finset.univ : Finset (Fin n)), square x i) ⊆
      Set.Ioc 0 M ×ˢ Set.Ioc 0 M := by
    intro p hp
    simp only [Set.mem_iUnion, Finset.mem_univ, exists_true_left] at hp
    obtain ⟨i, ⟨h1, h2⟩, h3, h4⟩ := hp
    have := le_A x i
    have := le_D x i
    exact ⟨⟨by linarith, h2.trans (hM i).1⟩, by linarith, h4.trans (hM i).2⟩
  have hvol := measure_mono (μ := (volume : Measure (ℝ × ℝ))) hsub
  rw [measure_biUnion_finset (f := square x) (by simpa using hdisj) (fun i _ => by
    unfold square; exact measurableSet_Ioc.prod measurableSet_Ioc)] at hvol
  simp only [square, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioc, sub_sub_cancel,
    sub_zero] at hvol
  rw [← ENNReal.ofReal_mul hM0'] at hvol
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      ENNReal.ofReal (x i) * ENNReal.ofReal (x i) = ENNReal.ofReal (x i ^ 2) := by
    intro i _
    rw [← ENNReal.ofReal_mul (hpos i).le, sq]
  rw [Finset.sum_congr rfl hterm, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _),
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg hM0' hM0')] at hvol
  nlinarith [hvol]

/-- Every sequence of `n ≥ 1` distinct positive reals has a monotone subsequence with sum at
least `(∑ xᵢ) / √n`. -/
theorem exists_monotone_sum_ge (hn : 0 < n) (hinj : Function.Injective x) (hpos : ∀ i, 0 < x i) :
    ∃ S ∈ monotonicSubsequenceSums x, (∑ i, x i) / Real.sqrt n ≤ S := by
  classical
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  set M := (Finset.univ : Finset (Fin n)).sup' hne fun i => max (A x i) (D x i) with hMdef
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_mem_eq_sup' hne fun i => max (A x i) (D x i)
  have hM : ∀ i, A x i ≤ M ∧ D x i ≤ M := fun i =>
    ⟨(le_max_left _ _).trans (Finset.le_sup' (fun i => max (A x i) (D x i)) (Finset.mem_univ i)),
     (le_max_right _ _).trans (Finset.le_sup' (fun i => max (A x i) (D x i)) (Finset.mem_univ i))⟩
  have hsq := sum_sq_le x hinj M hM hpos
  have hcs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n))) (f := x)
  rw [Finset.card_univ, Fintype.card_fin] at hcs
  have hM0 : 0 ≤ M := (hpos ⟨0, hn⟩).le.trans ((le_A x _).trans (hM _).1)
  have hsum0 : 0 ≤ ∑ i, x i := Finset.sum_nonneg fun i _ => (hpos i).le
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have key : (∑ i, x i) ≤ Real.sqrt n * M := by
    have h1 : (∑ i, x i) ^ 2 ≤ (Real.sqrt n * M) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      calc (∑ i, x i) ^ 2 ≤ n * ∑ i, x i ^ 2 := hcs
        _ ≤ n * M ^ 2 := by gcongr
    nlinarith [h1, hsum0, mul_nonneg hsqrt.le hM0]
  refine ⟨M, ?_, ?_⟩
  · rw [hMdef, hi₀]
    rcases le_total (A x i₀) (D x i₀) with h | h
    · rw [max_eq_right h]; exact D_mem x i₀
    · rw [max_eq_left h]; exact A_mem x i₀
  · rw [div_le_iff₀ hsqrt]; linarith

end Square

/-- Every constant `c ≤ 1` is admissible. -/
theorem mem_admissibleConstants_of_le_one {c : ℝ} (hc : c ≤ 1) : c ∈ admissibleConstants := by
  intro ε hε
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn x hinj hpos
  obtain ⟨S, hS, hle⟩ := exists_monotone_sum_ge x hn hinj hpos
  refine ⟨S, hS, le_trans ?_ hle⟩
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hsum0 : 0 ≤ ∑ i, x i := Finset.sum_nonneg fun i _ => (hpos i).le
  rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hsqrt]
  nlinarith

theorem erdos_1026.variants.lower_bound : 1 / Real.sqrt 2 ∈ admissibleConstants := by
  apply mem_admissibleConstants_of_le_one
  rw [div_le_one (by positivity)]
  exact Real.one_lt_sqrt_two.le

end Erdos1026
