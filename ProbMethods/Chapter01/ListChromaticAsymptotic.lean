import ProbMethods.Chapter01.ListChromatic
import ProbMethods.Chapter01.PropertyBUpper
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# §1.4 — Corollary 1.4.4, `ch(K_{n,n}) = (1 + o(1)) log₂ n`

Zhao, *Probabilistic Methods in Combinatorics*, Corollary 1.4.4. The list chromatic number of
`K_{n,n}` is `log₂ n` to leading order. Both bounds are already in this development, and the
corollary is the statement that they meet.

`PMC.listChromaticBipartite n` is the least `k` for which `K_{n,n}` is `k`-choosable; it is
well defined because `K_{n,n}` is `2n`-choosable (give every vertex its own colours), so the
set of admissible `k` is nonempty.

## The route

* **Upper bound, from Theorem 1.4.2** (`PMC.completeBipartiteChoosable_of_lt_two_pow`):
  `n < 2^{k-1}` implies `k`-choosable, so `listChromaticBipartite n ≤ ⌈log₂ n⌉ + 1`.
* **Lower bound, from Theorem 1.4.3 and Theorem 1.3.3.** `PMC.not_completeBipartiteChoosable_of_not_twoColorable`
  turns a non-2-colourable `k`-uniform hypergraph with `n` edges into a failure of
  `k`-choosability. Theorem 1.3.3 (task #56, `PMC.exists_not_twoColorable_card_le`) supplies one
  with at most `2k²2^k` edges, and edges may be *added* to a non-2-colourable hypergraph without
  making it 2-colourable — there are `C(k², k) ≫ 2k²2^k` available `k`-subsets of `[k²]`, so it
  can be padded to exactly `n` edges whenever `n ≥ 2k²2^k`. Hence
  `listChromaticBipartite n ≥ k + 1` for every `k` with `2k²2^k ≤ n`, i.e.
  `≥ log₂ n - 2log₂ k - O(1) = (1 - o(1)) log₂ n`.

The two together give the limit. Note the shape: the corollary is `o(1)`-asymptotic, but neither
input is — the asymptotics are entirely in the final squeeze, which is why this is publishable
as one bounded task on top of #56.
-/

open Finset

namespace PMC

section ListChromaticAsymptotic

/-- The list chromatic number of `K_{n,n}`: the least number of colours per list that always
suffices.

Defined as an `sInf` so that it is total with no side condition; the set is nonempty for every
`n` by Theorem 1.4.2 (`PMC.completeBipartiteChoosable_of_lt_two_pow` at any `k` with
`n < 2^{k-1}`), which is what keeps the value meaningful rather than the `sInf`-of-empty
default. -/
noncomputable def listChromaticBipartite (n : ℕ) : ℕ :=
  sInf {k | CompleteBipartiteChoosable n k}

/-- Choosability only gets easier with longer lists: shrink each `k`-list to a `j`-subset. A
colour from the sublist lies in the list. -/
private theorem choosable_mono_listSize {n j k : ℕ} (hjk : j ≤ k)
    (h : CompleteBipartiteChoosable n j) : CompleteBipartiteChoosable n k := by
  intro L hL
  choose L' hsub hcard using fun v => exists_subset_card_eq (hjk.trans_eq (hL v).symm)
  obtain ⟨f, hf, hne⟩ := h L' hcard
  exact ⟨f, fun v => hsub v (hf v), hne⟩

/-- Choosability passes to smaller complete bipartite graphs: give the extra vertices the list
`range k`, apply choosability, and restrict the colouring along `Fin.castLE`. This takes the
place of padding a hypergraph up to exactly `n` edges. -/
private theorem choosable_mono_vertices {m n k : ℕ} (hmn : m ≤ n)
    (h : CompleteBipartiteChoosable n k) : CompleteBipartiteChoosable m k := by
  intro L hL
  obtain ⟨L', hL'l, hL'r, hL'⟩ :
      ∃ L' : Fin n ⊕ Fin n → Finset ℕ,
        (∀ i : Fin m, L' (Sum.inl (Fin.castLE hmn i)) = L (Sum.inl i)) ∧
        (∀ i : Fin m, L' (Sum.inr (Fin.castLE hmn i)) = L (Sum.inr i)) ∧
        ∀ v, #(L' v) = k := by
    refine ⟨Sum.elim (fun i => if hi : (i : ℕ) < m then L (Sum.inl ⟨i, hi⟩) else range k)
      (fun i => if hi : (i : ℕ) < m then L (Sum.inr ⟨i, hi⟩) else range k),
      fun i => dif_pos i.2, fun i => dif_pos i.2, ?_⟩
    rintro (i | i) <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> split_ifs
    · exact hL _
    · exact card_range k
    · exact hL _
    · exact card_range k
  obtain ⟨f, hf, hne⟩ := h L' hL'
  refine ⟨Sum.elim (fun i => f (Sum.inl (Fin.castLE hmn i)))
    (fun i => f (Sum.inr (Fin.castLE hmn i))), ?_, fun i j => hne _ _⟩
  rintro (i | i)
  · exact hL'l i ▸ hf (Sum.inl (Fin.castLE hmn i))
  · exact hL'r i ▸ hf (Sum.inr (Fin.castLE hmn i))

/-- Theorem 1.4.2 at the first `k` it reaches: `n < 2 ^ (Nat.log 2 n + 1)`. -/
private theorem choosable_natLog_add_two (n : ℕ) :
    CompleteBipartiteChoosable n (Nat.log 2 n + 2) :=
  completeBipartiteChoosable_of_lt_two_pow (Nat.lt_pow_succ_log_self one_lt_two n)

/-- The upper bound in natural numbers. -/
private theorem listChromaticBipartite_le_natLog (n : ℕ) :
    listChromaticBipartite n ≤ Nat.log 2 n + 2 :=
  Nat.sInf_le (choosable_natLog_add_two n)

/-- The lower bound: `listChromaticBipartite n ≥ k + 1` whenever `2 k² 2^k ≤ n`, given
non-2-colourable `k`-uniform hypergraphs with at most `2 k² 2^k` edges. -/
private theorem lt_listChromaticBipartite_of_le
    (h : ∀ k : ℕ, 2 ≤ k → ∃ E : Finset (Finset (Fin (k * k))),
      (∀ e ∈ E, #e = k) ∧ #E ≤ 2 * (k * k) * 2 ^ k ∧ ¬ TwoColorable E)
    {n k : ℕ} (hk : 2 ≤ k) (hn : 2 * (k * k) * 2 ^ k ≤ n) : k < listChromaticBipartite n := by
  by_contra hle
  have hmem : CompleteBipartiteChoosable n (listChromaticBipartite n) :=
    Nat.sInf_mem (s := {k | CompleteBipartiteChoosable n k}) ⟨_, choosable_natLog_add_two n⟩
  obtain ⟨E, hEk, hEcard, hE⟩ := h k hk
  exact not_completeBipartiteChoosable_of_not_twoColorable hEk rfl hE
    (choosable_mono_vertices (hEcard.trans hn) (choosable_mono_listSize (not_lt.1 hle) hmem))

/-- From `L = 16` on, `L` leaves room for twice its own logarithm and a constant. -/
private theorem two_mul_natLog_add_five_le {L : ℕ} (hL : 16 ≤ L) : 2 * Nat.log 2 L + 5 ≤ L := by
  have hpow : ∀ a, 4 ≤ a → 2 * a + 5 ≤ 2 ^ a := by
    intro a ha
    induction a, ha using Nat.le_induction with
    | base => norm_num
    | succ a _ ih => rw [pow_succ]; omega
  have ha : 4 ≤ Nat.log 2 L := Nat.le_log_of_pow_le one_lt_two (by simpa using hL)
  exact (hpow _ ha).trans (Nat.pow_log_le_self 2 (by omega))

/-- The lower bound with `k = L - 2 log₂ L - 3` for `L = Nat.log 2 n`: since
`k ≤ L < 2 ^ (log₂ L + 1)`, this `k` satisfies `2 k² 2^k ≤ 2^L ≤ n`. -/
private theorem natLog_le_listChromaticBipartite_add
    (h : ∀ k : ℕ, 2 ≤ k → ∃ E : Finset (Finset (Fin (k * k))),
      (∀ e ∈ E, #e = k) ∧ #E ≤ 2 * (k * k) * 2 ^ k ∧ ¬ TwoColorable E)
    {n : ℕ} (hn : 2 ^ 16 ≤ n) :
    Nat.log 2 n ≤ listChromaticBipartite n + 2 * Nat.log 2 (Nat.log 2 n) + 2 := by
  have hL16 : 16 ≤ Nat.log 2 n := Nat.le_log_of_pow_le one_lt_two hn
  have haL := two_mul_natLog_add_five_le hL16
  have hLlt : Nat.log 2 n < 2 ^ (Nat.log 2 (Nat.log 2 n) + 1) :=
    Nat.lt_pow_succ_log_self one_lt_two _
  obtain ⟨k, hk⟩ : ∃ k, Nat.log 2 n = k + (2 * Nat.log 2 (Nat.log 2 n) + 3) :=
    ⟨Nat.log 2 n - (2 * Nat.log 2 (Nat.log 2 n) + 3), by omega⟩
  have hkpow : k ≤ 2 ^ (Nat.log 2 (Nat.log 2 n) + 1) := by omega
  have hbound : 2 * (k * k) * 2 ^ k ≤ n := by
    calc 2 * (k * k) * 2 ^ k
        ≤ 2 * (2 ^ (Nat.log 2 (Nat.log 2 n) + 1) * 2 ^ (Nat.log 2 (Nat.log 2 n) + 1)) * 2 ^ k := by
          gcongr
      _ = 2 ^ (k + (2 * Nat.log 2 (Nat.log 2 n) + 3)) := by ring
      _ = 2 ^ Nat.log 2 n := by rw [← hk]
      _ ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hlt := lt_listChromaticBipartite_of_le h (by omega) hbound
  omega

/-- `log₂ n` is less than `Nat.log 2 n + 1`. -/
private theorem logb_lt_natLog_add_one {n : ℕ} (hn : 0 < n) :
    Real.logb 2 n < Nat.log 2 n + 1 := by
  rw [Real.logb_lt_iff_lt_rpow one_lt_two (by exact_mod_cast hn)]
  have hlt : (n : ℝ) < 2 ^ (Nat.log 2 n + 1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self one_lt_two n
  have hcast : (Nat.log 2 n : ℝ) + 1 = ((Nat.log 2 n + 1 : ℕ) : ℝ) := by push_cast; rfl
  rwa [hcast, Real.rpow_natCast]

/-- `Nat.log 2 n` is at most `log₂ n`. -/
private theorem natLog_le_logb_two (n : ℕ) : (Nat.log 2 n : ℝ) ≤ Real.logb 2 n := by
  simpa using Real.natLog_le_logb n 2

/-- The real-variable limit behind the lower bound. -/
private theorem tendsto_sub_logb_div :
    Filter.Tendsto (fun y : ℝ => (y - 2 * Real.logb 2 y - 3) / y) Filter.atTop (nhds 1) := by
  have hlog : Filter.Tendsto (fun y : ℝ => Real.log y / y) Filter.atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hinv : Filter.Tendsto (fun y : ℝ => 3 / y) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Filter.tendsto_id
  have hlim : Filter.Tendsto (fun y : ℝ => 1 - 2 * (Real.log y / y / Real.log 2) - 3 / y)
      Filter.atTop (nhds (1 - 2 * (0 / Real.log 2) - 0)) :=
    (tendsto_const_nhds.sub ((hlog.div_const _).const_mul 2)).sub hinv
  rw [zero_div, mul_zero, sub_zero, sub_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with y hy
  rw [Real.logb]
  field_simp

/-- The real-variable limit behind the upper bound. -/
private theorem tendsto_add_two_div :
    Filter.Tendsto (fun y : ℝ => (y + 2) / y) Filter.atTop (nhds 1) := by
  have hinv : Filter.Tendsto (fun y : ℝ => 2 / y) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Filter.tendsto_id
  have hlim : Filter.Tendsto (fun y : ℝ => 1 + 2 / y) Filter.atTop (nhds (1 + 0)) :=
    tendsto_const_nhds.add hinv
  rw [add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with y hy
  field_simp

/-- The squeeze, with the bound of Theorem 1.3.3 as an explicit hypothesis. Both bounds sit
within `O(log₂ log₂ n)` of `log₂ n`, and only the eventual behaviour of the ratio matters. -/
theorem tendsto_of_exists_not_twoColorable
    (h : ∀ k : ℕ, 2 ≤ k → ∃ E : Finset (Finset (Fin (k * k))),
      (∀ e ∈ E, #e = k) ∧ #E ≤ 2 * (k * k) * 2 ^ k ∧ ¬ TwoColorable E) :
    Filter.Tendsto (fun n => (listChromaticBipartite n : ℝ) / Real.logb 2 n)
      Filter.atTop (nhds 1) := by
  have hx : Filter.Tendsto (fun n : ℕ => Real.logb 2 n) Filter.atTop Filter.atTop :=
    (Real.tendsto_logb_atTop one_lt_two).comp tendsto_natCast_atTop_atTop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_sub_logb_div.comp hx)
    (tendsto_add_two_div.comp hx) ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop (2 ^ 16), hx.eventually_gt_atTop 0] with n hn hpos
    have hL16 : 16 ≤ Nat.log 2 n := Nat.le_log_of_pow_le one_lt_two hn
    have hlower := natLog_le_listChromaticBipartite_add h hn
    have hlowerR : (Nat.log 2 n : ℝ) ≤ listChromaticBipartite n +
        2 * (Nat.log 2 (Nat.log 2 n) : ℕ) + 2 := by exact_mod_cast hlower
    have hlt := logb_lt_natLog_add_one (n := n) (by omega)
    have hlogL : Real.logb 2 (Nat.log 2 n) ≤ Real.logb 2 (Real.logb 2 n) :=
      Real.logb_le_logb_of_le one_lt_two (by exact_mod_cast (by omega : 0 < Nat.log 2 n))
        (natLog_le_logb_two n)
    have haL := natLog_le_logb_two (Nat.log 2 n)
    rw [Function.comp_apply]
    gcongr
    linarith
  · filter_upwards [hx.eventually_gt_atTop 0] with n hpos
    have hupper : (listChromaticBipartite n : ℝ) ≤ Nat.log 2 n + 2 := by
      exact_mod_cast listChromaticBipartite_le_natLog n
    have hlog := natLog_le_logb_two n
    rw [Function.comp_apply]
    gcongr
    linarith

/-- **Corollary 1.4.4.** `ch(K_{n,n}) / log₂ n → 1`. -/
theorem tendsto_listChromaticBipartite_div_logb :
    Filter.Tendsto (fun n => (listChromaticBipartite n : ℝ) / Real.logb 2 n)
      Filter.atTop (nhds 1) := by
  exact tendsto_of_exists_not_twoColorable fun _ hk => exists_not_twoColorable_card_le hk

end ListChromaticAsymptotic

end PMC
