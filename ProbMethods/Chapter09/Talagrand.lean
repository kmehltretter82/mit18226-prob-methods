import ProbMethods.Chapter09.BoundedDifferences
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.MeanInequalities

/-!
# §9.5 — Talagrand's inequality: the convex distance

Theorem 9.5.11: for `A ⊆ Ω₁ × ⋯ × Ωₙ` with a product probability measure,

    P(x ∈ A) · P(d_T(x, A) ≥ t) ≤ e^{-t²/4},

where `d_T` is Talagrand's **convex distance**. Its combinatorial applications are the reason
the inequality matters: unlike the bounded differences inequality, whose bound degrades as
`e^{-t²/n}`, this one has no `n` in the exponent.

This file sets up the distance and its basic properties, and states the inequality. **The
definitions are where the design choices are**, so they are recorded here rather than left to
whoever proves the analytic core:

* the sample space is the uniform product `Fin n → β`, as in §9.1 — not the fully general
  product of distinct factors with an arbitrary product measure. The notes' applications
  reach that generality by padding coordinates, the same device `Chapter09/
  ChromaticConcentration.lean` uses for graphs;
* `PMC.wHamDist` is the weighted Hamming distance and `PMC.wDistToSet` its distance to a set,
  defined to be `0` on the empty set so that it is total;
* `PMC.convexDist` is the supremum of `PMC.wDistToSet α` over the unit sphere of nonnegative
  weights, as a `sSup` — the set is nonempty and bounded above by `√n`
  (`PMC.wDistToSet_le_sqrt`), so the supremum is a genuine real number.

The inequality itself (`PMC.card_mul_card_filter_convexDist_le`) is published as a task. Its
proof is an induction on the number of coordinates using Hölder's inequality, together with
the elementary but delicate fact that `inf_{0≤λ≤1} e^{(1-λ)²/4} r^{-λ} ≤ 2 - r` for
`r ∈ (0,1]`; the notes do not prove it either.
-/

open Finset

namespace PMC

section Talagrand

variable {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β] {n : ℕ}

/-- The weighted Hamming distance: the total weight of the coordinates where `x` and `y`
differ. -/
def wHamDist (α : Fin n → ℝ) (x y : Fin n → β) : ℝ :=
  ∑ i ∈ (univ : Finset (Fin n)).filter fun i => x i ≠ y i, α i

lemma wHamDist_self (α : Fin n → ℝ) (x : Fin n → β) : wHamDist α x x = 0 := by
  rw [wHamDist, Finset.filter_false_of_mem, Finset.sum_empty]
  intro i _
  simp

lemma wHamDist_nonneg {α : Fin n → ℝ} (hα : ∀ i, 0 ≤ α i) (x y : Fin n → β) :
    0 ≤ wHamDist α x y :=
  Finset.sum_nonneg fun i _ => hα i

/-- The weighted distance from `x` to a set, taken to be `0` on the empty set. -/
noncomputable def wDistToSet (α : Fin n → ℝ) (A : Finset (Fin n → β)) (x : Fin n → β) : ℝ :=
  if h : A.Nonempty then A.inf' h (fun y => wHamDist α x y) else 0

lemma wDistToSet_nonneg {α : Fin n → ℝ} (hα : ∀ i, 0 ≤ α i) (A : Finset (Fin n → β))
    (x : Fin n → β) : 0 ≤ wDistToSet α A x := by
  rw [wDistToSet]
  by_cases h : A.Nonempty
  · rw [dif_pos h]
    obtain ⟨y, -, hy⟩ := Finset.exists_mem_eq_inf' h (fun y => wHamDist α x y)
    rw [hy]
    exact wHamDist_nonneg hα x y
  · rw [dif_neg h]

lemma wDistToSet_eq_zero_of_mem {α : Fin n → ℝ} (hα : ∀ i, 0 ≤ α i)
    {A : Finset (Fin n → β)} {x : Fin n → β} (hx : x ∈ A) : wDistToSet α A x = 0 := by
  have h : A.Nonempty := ⟨x, hx⟩
  rw [wDistToSet, dif_pos h]
  refine le_antisymm ?_ ?_
  · have := Finset.inf'_le (fun y => wHamDist α x y) hx
    rwa [wHamDist_self] at this
  · obtain ⟨y, -, hy⟩ := Finset.exists_mem_eq_inf' h (fun y => wHamDist α x y)
    rw [hy]
    exact wHamDist_nonneg hα x y

/-- **The weighted distance is at most `√n`** for a unit weight vector, by Cauchy–Schwarz on
the coordinates where the two points differ. This is what makes the supremum defining the
convex distance a real number. -/
lemma wDistToSet_le_sqrt {α : Fin n → ℝ} (hα : ∀ i, 0 ≤ α i) (hnorm : ∑ i, α i ^ 2 = 1)
    (A : Finset (Fin n → β)) (x : Fin n → β) : wDistToSet α A x ≤ Real.sqrt n := by
  classical
  have hbound : ∀ y : Fin n → β, wHamDist α x y ≤ Real.sqrt n := by
    intro y
    set D : Finset (Fin n) := (univ : Finset (Fin n)).filter fun i => x i ≠ y i with hD
    have hcs : (∑ i ∈ D, α i) ^ 2 ≤ #D * ∑ i ∈ D, α i ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have hle : ∑ i ∈ D, α i ^ 2 ≤ 1 := by
      rw [← hnorm]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun i _ _ => sq_nonneg _)
    have hcard : (#D : ℝ) ≤ n := by
      have := Finset.card_le_card (Finset.filter_subset (fun i => x i ≠ y i)
        (univ : Finset (Fin n)))
      rw [card_univ, Fintype.card_fin] at this
      exact_mod_cast this
    have hsq : (∑ i ∈ D, α i) ^ 2 ≤ (n : ℝ) := by
      calc (∑ i ∈ D, α i) ^ 2 ≤ #D * ∑ i ∈ D, α i ^ 2 := hcs
        _ ≤ (n : ℝ) * 1 := by
            refine mul_le_mul hcard hle (Finset.sum_nonneg fun i _ => sq_nonneg _) ?_
            positivity
        _ = (n : ℝ) := by ring
    have hnn : 0 ≤ ∑ i ∈ D, α i := Finset.sum_nonneg fun i _ => hα i
    rw [wHamDist, ← hD]
    calc ∑ i ∈ D, α i = Real.sqrt ((∑ i ∈ D, α i) ^ 2) := by
          rw [Real.sqrt_sq hnn]
      _ ≤ Real.sqrt n := Real.sqrt_le_sqrt hsq
  rw [wDistToSet]
  by_cases h : A.Nonempty
  · rw [dif_pos h]
    obtain ⟨y, -, hy⟩ := Finset.exists_mem_eq_inf' h (fun y => wHamDist α x y)
    rw [hy]
    exact hbound y
  · rw [dif_neg h]
    positivity

/-- The nonnegative unit weight vectors. -/
def unitWeights (n : ℕ) : Set (Fin n → ℝ) :=
  {α | (∀ i, 0 ≤ α i) ∧ (∑ i, α i ^ 2) = 1}

/-- **Talagrand's convex distance**: the largest weighted Hamming distance from `x` to `A`
over all nonnegative unit weight vectors. -/
noncomputable def convexDist (A : Finset (Fin n → β)) (x : Fin n → β) : ℝ :=
  sSup ((fun α => wDistToSet α A x) '' unitWeights n)

lemma unitWeights_nonempty (hn : 0 < n) : (unitWeights n).Nonempty := by
  have : NeZero n := ⟨by omega⟩
  refine ⟨fun i => if i = (0 : Fin n) then 1 else 0, fun i => by positivity, ?_⟩
  have hterm : ∀ i : Fin n, (if i = (0 : Fin n) then (1 : ℝ) else 0) ^ 2
      = if i = (0 : Fin n) then (1 : ℝ) else 0 := by
    intro i
    by_cases h : i = 0 <;> simp [h]
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  simp

lemma bddAbove_convexDist_image (A : Finset (Fin n → β)) (x : Fin n → β) :
    BddAbove ((fun α => wDistToSet α A x) '' unitWeights n) := by
  refine ⟨Real.sqrt n, ?_⟩
  rintro r ⟨α', hα', rfl⟩
  exact wDistToSet_le_sqrt hα'.1 hα'.2 A x

lemma convexDist_nonneg (hn : 0 < n) (A : Finset (Fin n → β)) (x : Fin n → β) :
    0 ≤ convexDist A x := by
  obtain ⟨α, hα⟩ := unitWeights_nonempty hn
  have hmem : wDistToSet α A x ∈ (fun α => wDistToSet α A x) '' unitWeights n := ⟨α, hα, rfl⟩
  exact le_trans (wDistToSet_nonneg hα.1 A x)
    (le_csSup (bddAbove_convexDist_image A x) hmem)

/-- The convex distance vanishes on `A`. -/
lemma convexDist_eq_zero_of_mem (hn : 0 < n) {A : Finset (Fin n → β)} {x : Fin n → β}
    (hx : x ∈ A) : convexDist A x = 0 := by
  refine le_antisymm ?_ (convexDist_nonneg hn A x)
  obtain ⟨α₀, hα₀⟩ := unitWeights_nonempty hn
  refine csSup_le ⟨_, ⟨α₀, hα₀, rfl⟩⟩ ?_
  rintro r ⟨α, hα, rfl⟩
  exact le_of_eq (wDistToSet_eq_zero_of_mem hα.1 hx)

/-! ### Proof of Talagrand's inequality

The induction runs on a vector-valued certificate rather than on `convexDist` itself: a vector
`z` *dominates* `x` against `A` when every nonnegative weight vector `α` sees `x` at weighted
distance at most `∑ i, α i * z i` from `A`. By Cauchy–Schwarz a dominating `z` bounds
`convexDist A x` by `‖z‖`, and dominating vectors are stable under the convex combinations the
induction needs, so the stronger statement

    ∑ x, exp(‖Z x‖² / 4) ≤ |β|^{2n} / #A

for a suitable choice of dominating vectors `Z x` goes through by peeling the last coordinate. -/

/-- `z` dominates the weighted distances from `x` to `A`. -/
private def Dominates {m : ℕ} (A : Finset (Fin m → β)) (x : Fin m → β) (z : Fin m → ℝ) :
    Prop :=
  ∀ α : Fin m → ℝ, (∀ i, 0 ≤ α i) → wDistToSet α A x ≤ ∑ i, α i * z i

/-- Second-order Taylor bound for `exp` on `[-1, 1]`, with the cubic error term. -/
private lemma exp_le_cubic {x : ℝ} (hx : |x| ≤ 1) :
    Real.exp x ≤ 1 + x + x ^ 2 / 2 + |x| ^ 3 * (2 / 9) := by
  have h := (abs_le.mp (Real.exp_bound hx (n := 3) (by norm_num))).2
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

private lemma exp_quarter_lt : Real.exp (1 / 4) < 4 / 3 := by
  have := Real.exp_bound_div_one_sub_of_interval' (x := 1 / 4) (by norm_num) (by norm_num)
  norm_num at this ⊢
  linarith

/-- The real-variable core of the induction step, after the substitution `r = e^{-s}`:
`inf_{μ ∈ [0,1]} e^{(1-μ)²/4} r^{-μ} ≤ 2 - r`. The choice is `μ = 1 - 2s` for `s ≤ 1/2`
and `μ = 0` otherwise. -/
private lemma exists_exp_add_exp_neg_le_two {s : ℝ} (hs : 0 ≤ s) :
    ∃ μ : ℝ, 0 ≤ μ ∧ μ ≤ 1 ∧ Real.exp ((1 - μ) ^ 2 / 4 + μ * s) + Real.exp (-s) ≤ 2 := by
  rcases le_or_gt s (1 / 2) with h | h
  · refine ⟨1 - 2 * s, by linarith, by linarith, ?_⟩
    have e : (1 - (1 - 2 * s)) ^ 2 / 4 + (1 - 2 * s) * s = s - s ^ 2 := by ring
    rw [e]
    have hu0 : 0 ≤ s - s ^ 2 := by nlinarith
    have hu : |s - s ^ 2| ≤ 1 := by
      rw [abs_of_nonneg hu0]
      nlinarith
    have h1 := exp_le_cubic hu
    have h2 := exp_le_cubic (x := -s) (by rw [abs_neg, abs_of_nonneg hs]; linarith)
    rw [abs_of_nonneg hu0] at h1
    rw [abs_neg, abs_of_nonneg hs] at h2
    have hc : (1 - s) ^ 3 ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    have hQ : -1 + s / 2 + 2 / 9 * ((1 - s) ^ 3 + 1) ≤ 0 := by nlinarith
    have hP : (s - s ^ 2) + (s - s ^ 2) ^ 2 / 2 + (s - s ^ 2) ^ 3 * (2 / 9)
        + (-s + (-s) ^ 2 / 2 + s ^ 3 * (2 / 9)) ≤ 0 := by
      have e2 : (s - s ^ 2) + (s - s ^ 2) ^ 2 / 2 + (s - s ^ 2) ^ 3 * (2 / 9)
          + (-s + (-s) ^ 2 / 2 + s ^ 3 * (2 / 9))
          = s ^ 3 * (-1 + s / 2 + 2 / 9 * ((1 - s) ^ 3 + 1)) := by ring
      rw [e2]
      exact mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hs 3) hQ
    linarith
  · refine ⟨0, le_refl _, zero_le_one, ?_⟩
    have e : (1 - (0 : ℝ)) ^ 2 / 4 + 0 * s = 1 / 4 := by ring
    rw [e]
    have h2 : Real.exp (-s) ≤ 2 / 3 := by
      have h3 : (3 / 2 : ℝ) ≤ Real.exp (1 / 2) := by
        have := Real.add_one_le_exp (1 / 2 : ℝ)
        linarith
      have h4 : Real.exp (-s) ≤ Real.exp (-(1 / 2)) := Real.exp_le_exp.mpr (by linarith)
      calc Real.exp (-s) ≤ Real.exp (-(1 / 2)) := h4
        _ = (Real.exp (1 / 2))⁻¹ := Real.exp_neg _
        _ ≤ (3 / 2)⁻¹ := inv_anti₀ (by norm_num) h3
        _ = 2 / 3 := by norm_num
    linarith [exp_quarter_lt]

/-- The induction step's numerical inequality in the scaled form it is used in: with slice
size `a`, projection size `b` and `K = |β|^{2n}`. -/
private lemma exists_exp_mul_rpow_le {a b K : ℝ} (ha : 0 < a) (hab : a ≤ b) (hK : 0 < K) :
    ∃ μ : ℝ, 0 ≤ μ ∧ μ ≤ 1 ∧
      Real.exp ((1 - μ) ^ 2 / 4) * ((K / a) ^ μ * (K / b) ^ (1 - μ)) ≤ K / b * (2 - a / b) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hs : 0 ≤ Real.log b - Real.log a := sub_nonneg.mpr (Real.log_le_log ha hab)
  obtain ⟨μ, hμ0, hμ1, hμ⟩ := exists_exp_add_exp_neg_le_two hs
  refine ⟨μ, hμ0, hμ1, ?_⟩
  have hKb : K / b = Real.exp (Real.log K - Real.log b) := by
    rw [Real.exp_sub, Real.exp_log hK, Real.exp_log hb]
  have e1 : (K / a) ^ μ * (K / b) ^ (1 - μ)
      = K / b * Real.exp (μ * (Real.log b - Real.log a)) := by
    rw [Real.rpow_def_of_pos (div_pos hK ha), Real.rpow_def_of_pos (div_pos hK hb),
      ← Real.exp_add, Real.log_div hK.ne' ha.ne', Real.log_div hK.ne' hb.ne', hKb,
      ← Real.exp_add]
    congr 1
    ring
  have e2 : a / b = Real.exp (-(Real.log b - Real.log a)) := by
    rw [neg_sub, Real.exp_sub, Real.exp_log ha, Real.exp_log hb]
  rw [e1, e2]
  have hKb0 : 0 < K / b := div_pos hK hb
  calc Real.exp ((1 - μ) ^ 2 / 4) * (K / b * Real.exp (μ * (Real.log b - Real.log a)))
      = K / b * Real.exp ((1 - μ) ^ 2 / 4 + μ * (Real.log b - Real.log a)) := by
        rw [Real.exp_add]
        ring
    _ ≤ K / b * (2 - Real.exp (-(Real.log b - Real.log a))) := by
        gcongr
        linarith

/-- Hölder's inequality with exponents `1/μ` and `1/(1-μ)`, in the form
`∑ uᵢ^μ vᵢ^{1-μ} ≤ (∑ uᵢ)^μ (∑ vᵢ)^{1-μ}`, via weighted AM–GM. -/
private lemma sum_rpow_mul_rpow_le {ι : Type*} (s : Finset ι) (u v : ι → ℝ)
    (hu : ∀ i ∈ s, 0 ≤ u i) (hv : ∀ i ∈ s, 0 ≤ v i) (hU : 0 < ∑ i ∈ s, u i)
    (hV : 0 < ∑ i ∈ s, v i) {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    ∑ i ∈ s, u i ^ μ * v i ^ (1 - μ) ≤ (∑ i ∈ s, u i) ^ μ * (∑ i ∈ s, v i) ^ (1 - μ) := by
  obtain ⟨U, hUdef⟩ : ∃ U, U = ∑ i ∈ s, u i := ⟨_, rfl⟩
  obtain ⟨V, hVdef⟩ : ∃ V, V = ∑ i ∈ s, v i := ⟨_, rfl⟩
  rw [← hUdef, ← hVdef]
  rw [← hUdef] at hU
  rw [← hVdef] at hV
  have hUμ : 0 < U ^ μ := Real.rpow_pos_of_pos hU μ
  have hVμ : 0 < V ^ (1 - μ) := Real.rpow_pos_of_pos hV _
  have key : ∀ i ∈ s, u i ^ μ * v i ^ (1 - μ)
      ≤ U ^ μ * V ^ (1 - μ) * (μ * (u i / U) + (1 - μ) * (v i / V)) := by
    intro i hi
    have h := Real.geom_mean_le_arith_mean2_weighted hμ0 (by linarith : 0 ≤ 1 - μ)
      (div_nonneg (hu i hi) hU.le) (div_nonneg (hv i hi) hV.le) (by ring)
    rw [Real.div_rpow (hu i hi) hU.le, Real.div_rpow (hv i hi) hV.le] at h
    calc u i ^ μ * v i ^ (1 - μ)
        = U ^ μ * V ^ (1 - μ) * (u i ^ μ / U ^ μ * (v i ^ (1 - μ) / V ^ (1 - μ))) := by
          field_simp
      _ ≤ U ^ μ * V ^ (1 - μ) * (μ * (u i / U) + (1 - μ) * (v i / V)) :=
          mul_le_mul_of_nonneg_left h (by positivity)
  calc ∑ i ∈ s, u i ^ μ * v i ^ (1 - μ)
      ≤ ∑ i ∈ s, U ^ μ * V ^ (1 - μ) * (μ * (u i / U) + (1 - μ) * (v i / V)) :=
        Finset.sum_le_sum key
    _ = U ^ μ * V ^ (1 - μ) * (μ * ((∑ i ∈ s, u i) / U) + (1 - μ) * ((∑ i ∈ s, v i) / V)) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          Finset.sum_div, Finset.sum_div]
    _ = U ^ μ * V ^ (1 - μ) := by
        rw [← hUdef, ← hVdef, div_self hU.ne', div_self hV.ne']
        ring

omit [Fintype β] [Nonempty β] in
private lemma wDistToSet_le_wHamDist {m : ℕ} (α : Fin m → ℝ) {C : Finset (Fin m → β)}
    {x y : Fin m → β} (hy : y ∈ C) : wDistToSet α C x ≤ wHamDist α x y := by
  rw [wDistToSet, dif_pos ⟨y, hy⟩]
  exact Finset.inf'_le _ hy

omit [Fintype β] [Nonempty β] in
private lemma exists_wDistToSet_eq {m : ℕ} (α : Fin m → ℝ) {C : Finset (Fin m → β)}
    (hC : C.Nonempty) (x : Fin m → β) : ∃ y ∈ C, wDistToSet α C x = wHamDist α x y := by
  obtain ⟨y, hy, h⟩ := Finset.exists_mem_eq_inf' hC (fun y => wHamDist α x y)
  exact ⟨y, hy, by rw [wDistToSet, dif_pos hC, h]⟩

omit [Fintype β] [Nonempty β] in
private lemma wHamDist_snoc {m : ℕ} (α : Fin (m + 1) → ℝ) (w y : Fin m → β) (ω ω' : β) :
    wHamDist α (Fin.snoc w ω) (Fin.snoc y ω')
      = wHamDist (fun i => α (Fin.castSucc i)) w y + if ω = ω' then 0 else α (Fin.last m) := by
  simp only [wHamDist, Finset.sum_filter]
  rw [Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last, ite_not]

private lemma sum_mul_snoc {m : ℕ} (α : Fin (m + 1) → ℝ) (v : Fin m → ℝ) (c : ℝ) :
    ∑ i, α i * (Fin.snoc v c : Fin (m + 1) → ℝ) i
      = ∑ i, α (Fin.castSucc i) * v i + α (Fin.last m) * c := by
  rw [Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

private lemma sum_sq_snoc {m : ℕ} (v : Fin m → ℝ) (c : ℝ) :
    ∑ i, (Fin.snoc v c : Fin (m + 1) → ℝ) i ^ 2 = ∑ i, v i ^ 2 + c ^ 2 := by
  rw [Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

/-- **The induction behind Talagrand's inequality.** Every nonempty `A` admits dominating
vectors `Z x` with `∑ x, exp(‖Z x‖² / 4) ≤ |β|^{2m} / #A`. -/
private lemma exists_dominates_sum_exp_le (m : ℕ) : ∀ A : Finset (Fin m → β), A.Nonempty →
    ∃ Z : (Fin m → β) → Fin m → ℝ, (∀ x, Dominates A x (Z x)) ∧
      ∑ x, Real.exp ((∑ i, Z x i ^ 2) / 4) ≤ ((Fintype.card β : ℝ) ^ m) ^ 2 / #A := by
  induction m with
  | zero =>
    intro A hA
    obtain ⟨y, hy⟩ := hA
    have hAy : A = {y} :=
      Finset.eq_singleton_iff_unique_mem.mpr ⟨hy, fun z _ => Subsingleton.elim z y⟩
    refine ⟨fun _ _ => 0, ?_, ?_⟩
    · intro x α hα
      rw [Subsingleton.elim x y, wDistToSet_eq_zero_of_mem hα hy]
      simp
    · subst hAy
      simp
  | succ m ih =>
    intro A hA
    set N : ℝ := (Fintype.card β : ℝ) ^ m with hN
    have hNpos : 0 < N := card_pos_pow m
    set B : Finset (Fin m → β) := univ.filter (fun w => ∃ ω, Fin.snoc w ω ∈ A) with hBdef
    set S : β → Finset (Fin m → β) := fun ω => univ.filter (fun w => Fin.snoc w ω ∈ A)
      with hSdef
    have hB : B.Nonempty := by
      obtain ⟨x, hx⟩ := hA
      refine ⟨Fin.init x, ?_⟩
      simp only [hBdef, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨x (Fin.last m), by rwa [Fin.snoc_init_self]⟩
    have hbpos : (0 : ℝ) < #B := by exact_mod_cast hB.card_pos
    have hSB : ∀ ω, S ω ⊆ B := by
      intro ω w hw
      simp only [hSdef, hBdef, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      exact ⟨ω, hw⟩
    have hcardA : (#A : ℝ) = ∑ ω, (#(S ω) : ℝ) := by
      have h1 : (#A : ℝ) = ∑ x : Fin (m + 1) → β, if x ∈ A then (1 : ℝ) else 0 := by
        rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]
      rw [h1, sum_snoc, Finset.sum_comm]
      refine Finset.sum_congr rfl fun ω _ => ?_
      rw [Finset.sum_boole]
    obtain ⟨ZB, hZBdom, hZBsum⟩ := ih B hB
    have hdomB : ∀ (w : Fin m → β) (α : Fin (m + 1) → ℝ), (∀ i, 0 ≤ α i) → ∀ ω,
        wDistToSet α A (Fin.snoc w ω)
          ≤ wDistToSet (fun i => α (Fin.castSucc i)) B w + α (Fin.last m) := by
      intro w α hα ω
      obtain ⟨y, hy, hyeq⟩ := exists_wDistToSet_eq (fun i => α (Fin.castSucc i)) hB w
      simp only [hBdef, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      obtain ⟨ω', hω'⟩ := hy
      rw [hyeq]
      calc wDistToSet α A (Fin.snoc w ω) ≤ wHamDist α (Fin.snoc w ω) (Fin.snoc y ω') :=
            wDistToSet_le_wHamDist α hω'
        _ ≤ wHamDist (fun i => α (Fin.castSucc i)) w y + α (Fin.last m) := by
            rw [wHamDist_snoc]
            gcongr
            split_ifs
            · exact hα _
            · exact le_rfl
    have hsumpos : ∀ Z : (Fin m → β) → Fin m → ℝ,
        0 < ∑ w, Real.exp ((∑ i, Z w i ^ 2) / 4) :=
      fun Z => Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
    have hslice : ∀ ω, ∃ Z' : (Fin m → β) → Fin (m + 1) → ℝ,
        (∀ w, Dominates A (Fin.snoc w ω) (Z' w)) ∧
        ∑ w, Real.exp ((∑ i, Z' w i ^ 2) / 4) ≤ N ^ 2 / #B * (2 - #(S ω) / #B) := by
      intro ω
      by_cases hS : (S ω).Nonempty
      · obtain ⟨ZS, hZSdom, hZSsum⟩ := ih (S ω) hS
        have hapos : (0 : ℝ) < #(S ω) := by exact_mod_cast hS.card_pos
        have hab : (#(S ω) : ℝ) ≤ #B := by exact_mod_cast Finset.card_le_card (hSB ω)
        obtain ⟨μ, hμ0, hμ1, hμ⟩ := exists_exp_mul_rpow_le hapos hab (pow_pos hNpos 2)
        refine ⟨fun w => Fin.snoc (fun i => μ * ZS w i + (1 - μ) * ZB w i) (1 - μ), ?_, ?_⟩
        · intro w α hα
          have hα' : ∀ i, 0 ≤ α (Fin.castSucc i) := fun i => hα _
          rw [sum_mul_snoc]
          have h1 : wDistToSet α A (Fin.snoc w ω)
              ≤ wDistToSet (fun i => α (Fin.castSucc i)) (S ω) w := by
            obtain ⟨y, hy, hyeq⟩ := exists_wDistToSet_eq (fun i => α (Fin.castSucc i)) hS w
            have hyA : Fin.snoc y ω ∈ A := by
              simpa only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and] using hy
            rw [hyeq]
            calc wDistToSet α A (Fin.snoc w ω) ≤ wHamDist α (Fin.snoc w ω) (Fin.snoc y ω) :=
                  wDistToSet_le_wHamDist α hyA
              _ = wHamDist (fun i => α (Fin.castSucc i)) w y := by
                  rw [wHamDist_snoc]
                  simp
          have h2 := hdomB w α hα ω
          have h3 := hZSdom w _ hα'
          have h4 := hZBdom w _ hα'
          have e : ∑ i, α (Fin.castSucc i) * (μ * ZS w i + (1 - μ) * ZB w i)
              = μ * ∑ i, α (Fin.castSucc i) * ZS w i
                + (1 - μ) * ∑ i, α (Fin.castSucc i) * ZB w i := by
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun i _ => ?_
            ring
          rw [e]
          have k1 := mul_le_mul_of_nonneg_left (h1.trans h3) hμ0
          have k2 := mul_le_mul_of_nonneg_left (h2.trans (add_le_add h4 le_rfl))
            (sub_nonneg.mpr hμ1)
          nlinarith
        · simp only [sum_sq_snoc]
          set PS : (Fin m → β) → ℝ := fun w => (∑ i, ZS w i ^ 2) / 4 with hPS
          set PB : (Fin m → β) → ℝ := fun w => (∑ i, ZB w i ^ 2) / 4 with hPB
          have hterm : ∀ w : Fin m → β,
              Real.exp ((∑ i, (μ * ZS w i + (1 - μ) * ZB w i) ^ 2 + (1 - μ) ^ 2) / 4)
                ≤ Real.exp ((1 - μ) ^ 2 / 4)
                  * (Real.exp (PS w) ^ μ * Real.exp (PB w) ^ (1 - μ)) := by
            intro w
            rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add, ← Real.exp_add]
            apply Real.exp_le_exp.mpr
            have hconv : ∑ i, (μ * ZS w i + (1 - μ) * ZB w i) ^ 2
                ≤ μ * ∑ i, ZS w i ^ 2 + (1 - μ) * ∑ i, ZB w i ^ 2 := by
              rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
              refine Finset.sum_le_sum fun i _ => ?_
              nlinarith [mul_nonneg (mul_nonneg hμ0 (sub_nonneg.mpr hμ1))
                (sq_nonneg (ZS w i - ZB w i))]
            simp only [hPS, hPB]
            nlinarith
          calc ∑ w, Real.exp ((∑ i, (μ * ZS w i + (1 - μ) * ZB w i) ^ 2 + (1 - μ) ^ 2) / 4)
              ≤ ∑ w, Real.exp ((1 - μ) ^ 2 / 4)
                  * (Real.exp (PS w) ^ μ * Real.exp (PB w) ^ (1 - μ)) :=
                Finset.sum_le_sum fun w _ => hterm w
            _ = Real.exp ((1 - μ) ^ 2 / 4)
                  * ∑ w, Real.exp (PS w) ^ μ * Real.exp (PB w) ^ (1 - μ) := by
                rw [Finset.mul_sum]
            _ ≤ Real.exp ((1 - μ) ^ 2 / 4)
                  * ((∑ w, Real.exp (PS w)) ^ μ * (∑ w, Real.exp (PB w)) ^ (1 - μ)) := by
                gcongr
                exact sum_rpow_mul_rpow_le _ _ _ (fun _ _ => (Real.exp_pos _).le)
                  (fun _ _ => (Real.exp_pos _).le) (hsumpos ZS) (hsumpos ZB) hμ0 hμ1
            _ ≤ Real.exp ((1 - μ) ^ 2 / 4)
                  * ((N ^ 2 / #(S ω)) ^ μ * (N ^ 2 / #B) ^ (1 - μ)) := by
                gcongr
            _ ≤ N ^ 2 / #B * (2 - #(S ω) / #B) := hμ
      · have hS0 : (#(S ω) : ℝ) = 0 := by
          rw [Finset.not_nonempty_iff_eq_empty.mp hS, Finset.card_empty, Nat.cast_zero]
        refine ⟨fun w => Fin.snoc (ZB w) 1, ?_, ?_⟩
        · intro w α hα
          rw [sum_mul_snoc, mul_one]
          exact (hdomB w α hα ω).trans
            (add_le_add (hZBdom w _ fun i => hα _) le_rfl)
        · simp only [sum_sq_snoc, one_pow]
          rw [hS0, zero_div, sub_zero]
          calc ∑ w, Real.exp ((∑ i, ZB w i ^ 2 + 1) / 4)
              = Real.exp (1 / 4) * ∑ w, Real.exp ((∑ i, ZB w i ^ 2) / 4) := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun w _ => ?_
                rw [← Real.exp_add]
                ring_nf
            _ ≤ 2 * (N ^ 2 / #B) := by
                gcongr
                linarith [exp_quarter_lt]
            _ = N ^ 2 / #B * 2 := by ring
    choose Z' hZ'dom hZ'sum using hslice
    refine ⟨fun x => Z' (x (Fin.last m)) (Fin.init x), ?_, ?_⟩
    · intro x
      have h := hZ'dom (x (Fin.last m)) (Fin.init x)
      rwa [Fin.snoc_init_self] at h
    · rw [sum_snoc]
      simp only [Fin.init_snoc, Fin.snoc_last]
      rw [Finset.sum_comm]
      have hApos : (0 : ℝ) < #A := by exact_mod_cast hA.card_pos
      calc ∑ ω, ∑ w, Real.exp ((∑ i, Z' ω w i ^ 2) / 4)
          ≤ ∑ ω, N ^ 2 / #B * (2 - #(S ω) / #B) :=
            Finset.sum_le_sum fun ω _ => hZ'sum ω
        _ = N ^ 2 / #B * (2 * Fintype.card β - #A / #B) := by
            rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_div, ← hcardA,
              Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            ring
        _ = (Fintype.card β * N) ^ 2 / #A
              - N ^ 2 * (Fintype.card β * #B - #A) ^ 2 / (#A * #B ^ 2) := by
            field_simp
            ring
        _ ≤ (Fintype.card β * N) ^ 2 / #A := by
            have : 0 ≤ N ^ 2 * (Fintype.card β * #B - #A) ^ 2 / (#A * #B ^ 2) := by
              positivity
            linarith
        _ = ((Fintype.card β : ℝ) ^ (m + 1)) ^ 2 / #A := by
            rw [hN, pow_succ]
            ring

/-- **Theorem 9.5.11 (Talagrand's inequality, general form).** In counting form:

    #A · #{x : d_T(x, A) ≥ t} ≤ |β|^{2n} · e^{-t²/4},

which is `P(x ∈ A) P(d_T(x,A) ≥ t) ≤ e^{-t²/4}` after dividing by `|β|^{2n}`. -/
theorem card_mul_card_filter_convexDist_le (hn : 0 < n) (A : Finset (Fin n → β)) {t : ℝ}
    (ht : 0 ≤ t) :
    (#A : ℝ) * #((univ : Finset (Fin n → β)).filter fun x => t ≤ convexDist A x)
      ≤ ((Fintype.card β : ℝ) ^ n) ^ 2 * Real.exp (-(t ^ 2) / 4) := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · rw [Finset.card_empty, Nat.cast_zero, zero_mul]
    positivity
  obtain ⟨Z, hZdom, hZsum⟩ := exists_dominates_sum_exp_le n A hA
  have hApos : (0 : ℝ) < #A := by exact_mod_cast hA.card_pos
  have hle : ∀ x ∈ (univ : Finset (Fin n → β)).filter (fun x => t ≤ convexDist A x),
      Real.exp (t ^ 2 / 4) ≤ Real.exp ((∑ i, Z x i ^ 2) / 4) := by
    intro x hx
    have htx : t ≤ convexDist A x := (Finset.mem_filter.mp hx).2
    have hcd : convexDist A x ≤ Real.sqrt (∑ i, Z x i ^ 2) := by
      obtain ⟨α₀, hα₀⟩ := unitWeights_nonempty hn
      refine csSup_le ⟨_, ⟨α₀, hα₀, rfl⟩⟩ ?_
      rintro r ⟨α, hα, rfl⟩
      calc wDistToSet α A x ≤ ∑ i, α i * Z x i := hZdom x α hα.1
        _ ≤ Real.sqrt (∑ i, α i ^ 2) * Real.sqrt (∑ i, Z x i ^ 2) :=
          Real.sum_mul_le_sqrt_mul_sqrt _ _ _
        _ = Real.sqrt (∑ i, Z x i ^ 2) := by rw [hα.2, Real.sqrt_one, one_mul]
    have h2 : t ^ 2 ≤ ∑ i, Z x i ^ 2 := by
      calc t ^ 2 ≤ Real.sqrt (∑ i, Z x i ^ 2) ^ 2 := pow_le_pow_left₀ ht (htx.trans hcd) 2
        _ = ∑ i, Z x i ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
    exact Real.exp_le_exp.mpr (by linarith)
  have hF : (#((univ : Finset (Fin n → β)).filter fun x => t ≤ convexDist A x) : ℝ)
      * Real.exp (t ^ 2 / 4) ≤ ((Fintype.card β : ℝ) ^ n) ^ 2 / #A := by
    calc (#((univ : Finset (Fin n → β)).filter fun x => t ≤ convexDist A x) : ℝ)
          * Real.exp (t ^ 2 / 4)
        = ∑ x ∈ (univ : Finset (Fin n → β)).filter (fun x => t ≤ convexDist A x),
            Real.exp (t ^ 2 / 4) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ x ∈ (univ : Finset (Fin n → β)).filter (fun x => t ≤ convexDist A x),
            Real.exp ((∑ i, Z x i ^ 2) / 4) := Finset.sum_le_sum hle
      _ ≤ ∑ x, Real.exp ((∑ i, Z x i ^ 2) / 4) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun _ _ _ => (Real.exp_pos _).le)
      _ ≤ ((Fintype.card β : ℝ) ^ n) ^ 2 / #A := hZsum
  rw [le_div_iff₀ hApos] at hF
  have e : Real.exp (-(t ^ 2) / 4) = (Real.exp (t ^ 2 / 4))⁻¹ := by
    rw [neg_div, Real.exp_neg]
  rw [e, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]
  linarith

end Talagrand

end PMC
