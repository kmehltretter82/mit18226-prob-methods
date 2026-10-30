import ProbMethods.Chapter04.BollobasThomason
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# §4.3 — Theorem 4.3.6, every non-trivial monotone property has a threshold

Zhao, *Probabilistic Methods in Combinatorics*, Definition 4.3.1 and Theorem 4.3.6
(Bollobás–Thomason 1987). `q` is a *threshold* for a sequence of monotone properties when

    P(Ω_{p_n} ∈ F) → 0  whenever  p_n / q_n → 0,      P(Ω_{p_n} ∈ F) → 1  whenever  p_n / q_n → ∞,

and the theorem is that a threshold always exists. The notes single this out as the reason
Lemma 4.3.7 is worth having ("The theorem follows from the next non-asymptotic claim"), so
this file is the asymptotic half of that pair; `PMC.sum_bweight_notMem_le_pow` is the other.

## The route

Take `q n` to be the `p` at which the property has probability exactly `1/2`.

* **It exists.** `p ↦ ∑_{X ∈ F n} bweight p X` is a polynomial in `p`, hence continuous, it is
  `0` at `p = 0` and `1` at `p = 1` — those two endpoint facts are exactly
  `PMC.notMem_empty_of_monotone` and `PMC.mem_univ_of_monotone`, which is what non-triviality
  is for — so the intermediate value theorem supplies `q n ∈ (0,1)` with value `1/2`.
* **Below the threshold.** Fix `m`. Once `p n ≤ q n / m`, antitonicity and Lemma 4.3.7 give

      P(Ω_{p n} ∉ F) ≥ P(Ω_{q n / m} ∉ F) ≥ P(Ω_{q n} ∉ F)^{1/m} = (1/2)^{1/m},

  so `P(Ω_{p n} ∈ F) ≤ 1 - (1/2)^{1/m}`. Letting `m → ∞` after `n → ∞` gives the limit `0`.
* **Above the threshold.** Once `p n ≥ m · q n`, the same lemma read forwards gives

      P(Ω_{p n} ∉ F) ≤ P(Ω_{p n / m} ∉ F)^m ≤ P(Ω_{q n} ∉ F)^m = (1/2)^m,

  so `P(Ω_{p n} ∈ F) ≥ 1 - 2^{-m}`, and again `m → ∞`.

Both directions need `p ↦ P(Ω_p ∉ F)` to be antitone, which is the non-strict form of task
#50, and Lemma 4.3.7, which is task #57. Nothing else.

Remark 4.3.3 in the notes — two thresholds differ by a bounded factor — is not part of this
statement; it is why the notes say "the" threshold.
-/

open Finset

namespace PMC

section ThresholdExists

variable {Ω : ℕ → Type} [∀ n, Fintype (Ω n)] [∀ n, DecidableEq (Ω n)]

/-- **Definition 4.3.1.** `q` is a threshold for the sequence of properties `F`. -/
def IsThreshold (F : ∀ n, Finset (Finset (Ω n))) (q : ℕ → ℝ) : Prop :=
  ∀ p : ℕ → ℝ, (∀ n, p n ∈ Set.Icc (0 : ℝ) 1) →
    (Filter.Tendsto (fun n => p n / q n) Filter.atTop (nhds 0) →
        Filter.Tendsto (fun n => ∑ X ∈ F n, bweight (p n) X) Filter.atTop (nhds 0)) ∧
      (Filter.Tendsto (fun n => p n / q n) Filter.atTop Filter.atTop →
        Filter.Tendsto (fun n => ∑ X ∈ F n, bweight (p n) X) Filter.atTop (nhds 1))

/-! ### One property: the point where the probability is `1/2` -/

/-- `P(Ω_p ∈ F) + P(Ω_p ∉ F) = 1`. -/
private lemma sum_bweight_add_sum_bweight_notMem {α : Type*} [Fintype α] [DecidableEq α]
    (F : Finset (Finset α)) (p : ℝ) :
    (∑ X ∈ F, bweight p X)
      + ∑ X ∈ (univ : Finset α).powerset.filter (fun X => X ∉ F), bweight p X = 1 := by
  have hset : (univ : Finset α).powerset.filter (fun X => X ∈ F) = F := by
    ext X
    simp
  have hsplit := Finset.sum_filter_add_sum_filter_not (univ : Finset α).powerset
    (fun X => X ∈ F) (bweight p)
  rwa [hset, sum_bweight] at hsplit

/-- `P(Ω_p ∈ F)` is a polynomial in `p`, hence continuous. -/
private lemma continuous_sum_bweight {α : Type*} [Fintype α] [DecidableEq α]
    (F : Finset (Finset α)) : Continuous fun p : ℝ => ∑ X ∈ F, bweight p X := by
  refine continuous_finsetSum _ fun X _ => ?_
  unfold bweight
  fun_prop

/-- A family avoiding `∅` has probability `0` at `p = 0`. -/
private lemma sum_bweight_zero_of_empty_notMem {α : Type*} [Fintype α] [DecidableEq α]
    {F : Finset (Finset α)} (hF : (∅ : Finset α) ∉ F) : ∑ X ∈ F, bweight (0 : ℝ) X = 0 := by
  refine Finset.sum_eq_zero fun X hX => ?_
  have hne : X.Nonempty := Finset.nonempty_iff_ne_empty.mpr fun h => hF (h ▸ hX)
  rw [bweight, zero_pow (Finset.card_ne_zero.mpr hne), zero_mul]

/-- A family containing `univ` has probability `1` at `p = 1`. -/
private lemma sum_bweight_one_of_univ_mem {α : Type*} [Fintype α] [DecidableEq α]
    {F : Finset (Finset α)} (hF : (univ : Finset α) ∈ F) : ∑ X ∈ F, bweight (1 : ℝ) X = 1 := by
  rw [Finset.sum_eq_single_of_mem univ hF]
  · simp [bweight]
  · intro X _ hX
    have hlt : #X < Fintype.card α := by
      rw [← Finset.card_univ]
      exact Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hX)
    rw [bweight, sub_self, zero_pow (by omega), mul_zero]

/-- A non-trivial monotone family has probability exactly `1/2` at some `q ∈ (0,1)`. -/
private lemma exists_sum_bweight_eq_half {α : Type*} [Fintype α] [DecidableEq α]
    {F : Finset (Finset α)} (hF : IsMonotoneFamily F) (hne : F.Nonempty)
    (hnotall : F ≠ (univ : Finset (Finset α))) :
    ∃ q ∈ Set.Ioo (0 : ℝ) 1, ∑ X ∈ F, bweight q X = 1 / 2 := by
  have h0 := sum_bweight_zero_of_empty_notMem (notMem_empty_of_monotone hF hnotall)
  have h1 := sum_bweight_one_of_univ_mem (mem_univ_of_monotone hF hne)
  have hhalf : (1 / 2 : ℝ) ∈ (fun p : ℝ => ∑ X ∈ F, bweight p X) '' Set.Icc 0 1 := by
    refine intermediate_value_Icc zero_le_one (continuous_sum_bweight F).continuousOn ?_
    simp only [Set.mem_Icc, h0, h1]
    norm_num
  obtain ⟨q, ⟨hq0, hq1⟩, hval⟩ := hhalf
  have hval' : ∑ X ∈ F, bweight q X = 1 / 2 := hval
  refine ⟨q, ⟨lt_of_le_of_ne hq0 ?_, lt_of_le_of_ne hq1 ?_⟩, hval'⟩
  · rintro rfl
    rw [h0] at hval'
    norm_num at hval'
  · rintro rfl
    rw [h1] at hval'
    norm_num at hval'

/-! ### One property: the two estimates

`g` below stands for `p ↦ P(Ω_p ∉ F)`, of which only nonnegativity, antitonicity and
Lemma 4.3.7 are used, together with `g q = 1/2`. -/

/-- Below the threshold: if `c ^ m < 1/2` and `p ≤ q / m`, then `c < g p`. -/
private lemma lt_of_le_div_of_pow_lt_half {g : ℝ → ℝ}
    (hg0 : ∀ p, 0 ≤ p → p ≤ 1 → 0 ≤ g p) (hanti : AntitoneOn g (Set.Icc 0 1))
    (hbt : ∀ p, 0 ≤ p → p ≤ 1 → ∀ m : ℕ, 1 ≤ m → g p ≤ g (p / m) ^ m)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hgq : g q = 1 / 2)
    {c : ℝ} {m : ℕ} (hm : 1 ≤ m) (hcm : c ^ m < 1 / 2)
    {p : ℝ} (hp0 : 0 ≤ p) (hpq : p ≤ q / m) : c < g p := by
  by_contra hle
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hqm0 : 0 ≤ q / m := div_nonneg hq0 (by linarith)
  have hqm1 : q / m ≤ 1 := (div_le_self hq0 hm').trans hq1
  have h1 : g (q / m) ≤ g p := hanti ⟨hp0, hpq.trans hqm1⟩ ⟨hqm0, hqm1⟩ hpq
  have h2 : g (q / m) ^ m ≤ c ^ m :=
    pow_le_pow_left₀ (hg0 _ hqm0 hqm1) (h1.trans (not_lt.mp hle)) m
  have h3 := hbt q hq0 hq1 m hm
  linarith

/-- Above the threshold: if `q ≤ p / m`, then `g p ≤ (1/2) ^ m`. -/
private lemma le_half_pow_of_le_div {g : ℝ → ℝ}
    (hg0 : ∀ p, 0 ≤ p → p ≤ 1 → 0 ≤ g p) (hanti : AntitoneOn g (Set.Icc 0 1))
    (hbt : ∀ p, 0 ≤ p → p ≤ 1 → ∀ m : ℕ, 1 ≤ m → g p ≤ g (p / m) ^ m)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hgq : g q = 1 / 2)
    {m : ℕ} (hm : 1 ≤ m) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hqp : q ≤ p / m) :
    g p ≤ (1 / 2) ^ m := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hpm0 : 0 ≤ p / m := div_nonneg hp0 (by linarith)
  have hpm1 : p / m ≤ 1 := (div_le_self hp0 hm').trans hp1
  calc g p ≤ g (p / m) ^ m := hbt p hp0 hp1 m hm
    _ ≤ g q ^ m := pow_le_pow_left₀ (hg0 _ hpm0 hpm1) (hanti ⟨hq0, hq1⟩ ⟨hpm0, hpm1⟩ hqp) m
    _ = (1 / 2) ^ m := by rw [hgq]

/-! ### The sequence of properties -/

/-- If `p n / q n → 0` then `g n (p n) → 1`. -/
private lemma tendsto_one_of_div_tendsto_zero {g : ℕ → ℝ → ℝ}
    (hg0 : ∀ n p, 0 ≤ p → p ≤ 1 → 0 ≤ g n p) (hg1 : ∀ n p, 0 ≤ p → p ≤ 1 → g n p ≤ 1)
    (hanti : ∀ n, AntitoneOn (g n) (Set.Icc 0 1))
    (hbt : ∀ n p, 0 ≤ p → p ≤ 1 → ∀ m : ℕ, 1 ≤ m → g n p ≤ g n (p / m) ^ m)
    {q : ℕ → ℝ} (hq : ∀ n, q n ∈ Set.Ioo (0 : ℝ) 1) (hgq : ∀ n, g n (q n) = 1 / 2)
    {p : ℕ → ℝ} (hp : ∀ n, p n ∈ Set.Icc (0 : ℝ) 1)
    (h : Filter.Tendsto (fun n => p n / q n) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => g n (p n)) Filter.atTop (nhds 1) := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => Filter.Eventually.of_forall fun n =>
    (hg1 n _ (hp n).1 (hp n).2).trans_lt ha⟩
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (one_half_pos (α := ℝ))
    (max_lt ha one_pos : max a 0 < 1)
  have hm1 : 1 ≤ m := by
    refine Nat.one_le_iff_ne_zero.mpr ?_
    rintro rfl
    norm_num at hm
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
  filter_upwards [h.eventually_lt_const (show (0 : ℝ) < 1 / m by positivity)] with n hn
  have hlt : p n < 1 / m * q n := (div_lt_iff₀ (hq n).1).1 hn
  have hle : p n ≤ q n / m := by
    have e : q n / m = 1 / m * q n := by ring
    linarith
  exact (le_max_left a 0).trans_lt <| lt_of_le_div_of_pow_lt_half (hg0 n) (hanti n) (hbt n)
    (hq n).1.le (hq n).2.le (hgq n) hm1 hm (hp n).1 hle

/-- If `p n / q n → ∞` then `g n (p n) → 0`. -/
private lemma tendsto_zero_of_div_tendsto_atTop {g : ℕ → ℝ → ℝ}
    (hg0 : ∀ n p, 0 ≤ p → p ≤ 1 → 0 ≤ g n p)
    (hanti : ∀ n, AntitoneOn (g n) (Set.Icc 0 1))
    (hbt : ∀ n p, 0 ≤ p → p ≤ 1 → ∀ m : ℕ, 1 ≤ m → g n p ≤ g n (p / m) ^ m)
    {q : ℕ → ℝ} (hq : ∀ n, q n ∈ Set.Ioo (0 : ℝ) 1) (hgq : ∀ n, g n (q n) = 1 / 2)
    {p : ℕ → ℝ} (hp : ∀ n, p n ∈ Set.Icc (0 : ℝ) 1)
    (h : Filter.Tendsto (fun n => p n / q n) Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun n => g n (p n)) Filter.atTop (nhds 0) := by
  refine tendsto_order.2 ⟨fun a ha => Filter.Eventually.of_forall fun n =>
    ha.trans_le (hg0 n _ (hp n).1 (hp n).2), fun a ha => ?_⟩
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one ha (one_half_lt_one (α := ℝ))
  have hmpos : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  filter_upwards [h.eventually_ge_atTop ((m + 1 : ℕ) : ℝ)] with n hn
  have hmul : ((m + 1 : ℕ) : ℝ) * q n ≤ p n := (le_div_iff₀ (hq n).1).1 hn
  have hle : q n ≤ p n / (m + 1 : ℕ) := (le_div_iff₀ hmpos).2 (by linarith)
  calc g n (p n) ≤ (1 / 2) ^ (m + 1) :=
        le_half_pow_of_le_div (hg0 n) (hanti n) (hbt n) (hq n).1.le (hq n).2.le (hgq n)
          (Nat.le_add_left 1 m) (hp n).1 (hp n).2 hle
    _ ≤ (1 / 2) ^ m := pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ m)
    _ < a := hm

/-- Theorem 4.3.6 with its two inputs as hypotheses: strict monotonicity of
`p ↦ P(Ω_p ∈ F n)` (Theorem 4.3.5) and the bound `P(Ω_p ∉ F n) ≤ P(Ω_{p/m} ∉ F n) ^ m`
(Lemma 4.3.7). -/
theorem exists_isThreshold_of_monotone_of_pow_bound (F : ∀ n, Finset (Finset (Ω n)))
    (hmono : ∀ n, IsMonotoneFamily (F n)) (hne : ∀ n, (F n).Nonempty)
    (hnotall : ∀ n, F n ≠ (univ : Finset (Finset (Ω n))))
    (hstrict : ∀ n, StrictMonoOn (fun p : ℝ => ∑ S ∈ F n, bweight p S) (Set.Icc (0 : ℝ) 1))
    (hbt : ∀ n (p : ℝ), 0 ≤ p → p ≤ 1 → ∀ m : ℕ, 1 ≤ m →
      (∑ X ∈ (univ : Finset (Ω n)).powerset.filter (fun X => X ∉ F n), bweight p X)
        ≤ (∑ X ∈ (univ : Finset (Ω n)).powerset.filter (fun X => X ∉ F n),
            bweight (p / m) X) ^ m) :
    ∃ q : ℕ → ℝ, (∀ n, q n ∈ Set.Ioo (0 : ℝ) 1) ∧ IsThreshold F q := by
  choose q hq hqval using fun n => exists_sum_bweight_eq_half (hmono n) (hne n) (hnotall n)
  let g : ℕ → ℝ → ℝ := fun n p =>
    ∑ X ∈ (univ : Finset (Ω n)).powerset.filter (fun X => X ∉ F n), bweight p X
  have hadd : ∀ n p, (∑ X ∈ F n, bweight p X) + g n p = 1 := fun n p =>
    sum_bweight_add_sum_bweight_notMem (F n) p
  have hf0 : ∀ n (p : ℝ), 0 ≤ p → p ≤ 1 → 0 ≤ ∑ X ∈ F n, bweight p X := fun n _ hp0 hp1 =>
    Finset.sum_nonneg fun X _ => bweight_nonneg hp0 hp1 X
  have hg0 : ∀ n p, 0 ≤ p → p ≤ 1 → 0 ≤ g n p := fun n _ hp0 hp1 =>
    Finset.sum_nonneg fun X _ => bweight_nonneg hp0 hp1 X
  have hg1 : ∀ n p, 0 ≤ p → p ≤ 1 → g n p ≤ 1 := fun n p hp0 hp1 => by
    linarith [hadd n p, hf0 n p hp0 hp1]
  have hanti : ∀ n, AntitoneOn (g n) (Set.Icc 0 1) := fun n a ha b hb hab => by
    have hle : ∑ X ∈ F n, bweight a X ≤ ∑ X ∈ F n, bweight b X :=
      (hstrict n).monotoneOn ha hb hab
    linarith [hadd n a, hadd n b]
  have hgq : ∀ n, g n (q n) = 1 / 2 := fun n => by
    linarith [hadd n (q n), hqval n]
  refine ⟨q, hq, fun p hp => ⟨fun h => ?_, fun h => ?_⟩⟩
  · have hlim := (tendsto_one_of_div_tendsto_zero hg0 hg1 hanti hbt hq hgq hp h).const_sub 1
    rw [sub_self] at hlim
    exact hlim.congr fun n => by linarith [hadd n (p n)]
  · have hlim := (tendsto_zero_of_div_tendsto_atTop hg0 hanti hbt hq hgq hp h).const_sub 1
    rw [sub_zero] at hlim
    exact hlim.congr fun n => by linarith [hadd n (p n)]

/-- **Theorem 4.3.6 (Bollobás–Thomason 1987).** Every sequence of non-trivial monotone
properties has a threshold. -/
theorem exists_isThreshold (F : ∀ n, Finset (Finset (Ω n)))
    (hmono : ∀ n, IsMonotoneFamily (F n)) (hne : ∀ n, (F n).Nonempty)
    (hnotall : ∀ n, F n ≠ (univ : Finset (Finset (Ω n)))) :
    ∃ q : ℕ → ℝ, (∀ n, q n ∈ Set.Ioo (0 : ℝ) 1) ∧ IsThreshold F q := by
  exact exists_isThreshold_of_monotone_of_pow_bound F hmono hne hnotall
    (fun n => strictMonoOn_sum_bweight (F n) (hmono n) (hne n) (hnotall n))
    (fun n _ hp0 hp1 _ hm => sum_bweight_notMem_le_pow (hmono n) hp0 hp1 hm)

end ThresholdExists

end PMC
