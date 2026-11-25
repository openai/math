import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import OAI.LinearAlgebra.SpectralBooks.PermutationCoverBound
import OAI.LinearAlgebra.SpectralBooks.BalancedWords
import Mathlib.Tactic

/-! # Covering ordered pairs by permutations

The counting argument in the permutation-stretch lemma applies to any finite
transitive action. We count lists missing each prescribed ordered pair and
take a union bound before retaining the distinct entries of a successful list.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Finset

variable (G X : Type*) [Group G] [Fintype G] [Fintype X] [MulAction G X]
    [MulAction.IsPretransitive G X]

/-- The number of group elements sending a fixed point to a given target
times the size of the homogeneous space is the order of the group. -/
theorem card_smul_fiber_mul_card (x y : X) [DecidableEq X] :
    Fintype.card {g : G // g • x = y} * Fintype.card X = Fintype.card G := by
  classical
  have h (z : X) :
      Fintype.card {g : G // g • x = z} = Fintype.card {g : G // g • x = y} := by
    obtain ⟨t, ht⟩ := MulAction.exists_smul_eq G z y
    exact Fintype.card_congr ((Equiv.mulLeft t).subtypeEquiv (fun g => by
      change g • x = z ↔ (t * g) • x = y
      rw [mul_smul, ← ht]
      exact (MulAction.injective t).eq_iff.symm))
  have hsum := Fintype.card_congr (Equiv.sigmaFiberEquiv (fun g : G => g • x))
  rw [Fintype.card_sigma] at hsum
  simpa [h, mul_comm] using hsum

/-- If the union bound for lists of length `M` is strictly less than one,
there is a set of at most `M` group elements carrying every point to every
other point. -/
theorem exists_action_cover_of_missedPairs_lt_one [Nonempty X] (M : ℕ)
    (hM : (Fintype.card X : ℝ)^2 * (1 - 1 / (Fintype.card X : ℝ))^M < 1) :
    ∃ P : Finset G, P.card ≤ M ∧ ∀ x y : X, ∃ g ∈ P, g • x = y := by
  classical
  let N : ℝ := Fintype.card X
  let Q : ℝ := Fintype.card G
  have hN : 0 < N := by dsimp [N]; exact_mod_cast (Fintype.card_pos (α := X))
  have hQ : 0 < Q := by dsimp [Q]; exact_mod_cast (Fintype.card_pos (α := G))
  let misses (p : X × X) : Finset G := univ.filter (fun g => g • p.1 ≠ p.2)
  have hmisses (p : X × X) : ((misses p).card : ℝ) = Q * (1 - 1 / N) := by
    let good := Fintype.card {g : G // g • p.1 = p.2}
    have hgood : (good : ℝ) * N = Q := by
      dsimp [good, N, Q]
      exact_mod_cast card_smul_fiber_mul_card G X p.1 p.2
    have htotal : good + (misses p).card = Fintype.card G := by
      simpa [good, misses, Fintype.card_subtype] using
        (card_filter_add_card_filter_not (s := univ) (fun g : G => g • p.1 = p.2))
    have ht : (good : ℝ) + (misses p).card = Q := by dsimp [Q]; exact_mod_cast htotal
    field_simp [hN.ne']
    nlinarith [congrArg (fun t : ℝ => t * N) ht]
  let bad (p : X × X) : Finset (Fin M → G) := Fintype.piFinset (fun _ => misses p)
  have hbad (p : X × X) : ((bad p).card : ℝ) = (Q * (1 - 1 / N))^M := by
    rw [show (bad p).card = (misses p).card ^ M from Fintype.card_piFinset_const _ _, Nat.cast_pow,
      hmisses]
  have hcount : (((univ.biUnion bad).card : ℕ) : ℝ) ≤ N^2 * (Q * (1 - 1 / N))^M := by
    calc
      _ ≤ ((∑ p, (bad p).card : ℕ) : ℝ) := by exact_mod_cast card_biUnion_le
      _ = _ := by simp [Nat.cast_sum, hbad, Fintype.card_prod, N, pow_two]
  have hall : (univ.biUnion bad).card < Fintype.card (Fin M → G) := by
    have hp : 0 < Q^M := pow_pos hQ _
    change N^2 * (1 - 1 / N)^M < 1 at hM
    have hlt : (((univ.biUnion bad).card : ℕ) : ℝ) < Q^M := calc
      _ ≤ _ := hcount
      _ = (N^2 * (1 - 1 / N)^M) * Q^M := by rw [mul_pow]; ring
      _ < Q^M := by simpa using mul_lt_mul_of_pos_right hM hp
    rw [Fintype.card_pi_const]
    dsimp [Q] at hlt
    exact_mod_cast hlt
  obtain ⟨f, hf⟩ : ∃ f, f ∉ univ.biUnion bad := by
    by_contra! h
    exact (card_lt_iff_ne_univ _).mp hall (eq_univ_of_forall h)
  refine ⟨univ.image f, ?_, fun x y => ?_⟩
  · simpa using card_image_le (s := univ) (f := f)
  · have hxy : f ∉ bad (x,y) := fun h => hf (mem_biUnion.mpr ⟨(x,y), mem_univ _, h⟩)
    have hex : ∃ j, f j • x = y := by
      by_contra! h
      exact hxy (Fintype.mem_piFinset.mpr (fun i => mem_filter.mpr ⟨mem_univ _, h i⟩))
    obtain ⟨j, hj⟩ := hex
    exact ⟨f j, mem_image_of_mem f (mem_univ _), hj⟩

/-- The cover size in the proof of the permutation-stretch lemma, with the
manuscript's base-two logarithm. -/
theorem exists_small_action_cover [Nonempty X] :
    ∃ P : Finset G,
      P.card ≤ ⌈3 * (Fintype.card X : ℝ) * Real.logb 2 (2 * (Fintype.card X : ℝ))⌉₊ ∧
      ∀ x y : X, ∃ g ∈ P, g • x = y :=
  exists_action_cover_of_missedPairs_lt_one G X _ (missedPairs_lt_one _ Fintype.card_pos)

/-- The small cover consists of actual coordinate permutations of a prescribed
word type. Constant letter counts give the balanced words of the manuscript. -/
theorem exists_word_permutation_cover (ι α : Type*) [Fintype ι] [Fintype α] [DecidableEq α]
    (counts : α → ℕ) [Nonempty (WordsOfContent ι α counts)] :
    let N := Fintype.card (WordsOfContent ι α counts)
    ∃ P : Finset (Equiv.Perm ι), P.card ≤ ⌈3 * (N : ℝ) * Real.logb 2 (2 * (N : ℝ))⌉₊ ∧
      ∀ x y : WordsOfContent ι α counts, ∃ π ∈ P, ∀ i, x.1 (π.symm i) = y.1 i := by
  classical
  obtain ⟨P, hc, h⟩ := exists_small_action_cover (Equiv.Perm ι) (WordsOfContent ι α counts)
  refine ⟨P, hc, fun x y => ?_⟩
  obtain ⟨π, hπ, hxy⟩ := h x y
  exact ⟨π, hπ, fun i => congrArg (fun w : WordsOfContent ι α counts => w.1 i) hxy⟩

open Filter
open scoped Topology

/-- The balanced-word permutation covers in the stretch argument. Along the
multiples `m = R * k`, their base-two logarithms divided by `m` tend to
`log₂ R`. The covering equation has the orientation used in the restriction
at the common site. -/
theorem exists_balanced_permutation_covers {R : ℕ} (hR : 0 < R) :
    ∃ P : (k : ℕ) → Finset (Equiv.Perm (Fin (R * k))),
      (∀ k (i j : BalancedWords R k), ∃ π ∈ P k, j.1 ∘ π = i.1) ∧
      Tendsto (fun k : ℕ => Real.logb 2 (P k).card / ((R : ℝ) * k)) atTop (𝓝 (Real.logb 2 R)) := by
  classical
  let W := BalancedWords R
  have hpos (k : ℕ) : 0 < Fintype.card (W k) := Nat.pos_of_mul_pos_right
    ((card_balancedWords_mul_factorial R k) ▸ Nat.factorial_pos _)
  let (k : ℕ) : Nonempty (W k) := Fintype.card_pos_iff.mp (hpos k)
  choose P hsize hcover using
    (fun k : ℕ => exists_small_action_cover (Equiv.Perm (Fin (R * k))) (W k))
  refine ⟨P, ?_, ?_⟩
  · intro k i j
    obtain ⟨π, hπ, eq⟩ := hcover k i j
    refine ⟨π, hπ, funext fun t => ?_⟩
    have ht := (congrArg (fun w : W k => w.1 (π t)) eq).symm
    change j.1 (π t) = i.1 (π.symm (π t)) at ht
    simpa using ht
  · have hlo (k : ℕ) : Fintype.card (W k) ≤ (P k).card := by
      let x : W k := Classical.choice (Fintype.card_pos_iff.mp (hpos k))
      have hsurj : Function.Surjective (fun p : P k => p.1 • x) := by
        intro y
        obtain ⟨p, hp, h⟩ := hcover k x y
        exact ⟨⟨p, hp⟩, h⟩
      simpa using Fintype.card_le_of_surjective _ hsurj
    have htop : Tendsto (fun k : ℕ => R * k) atTop atTop := by
      exact tendsto_atTop_mono (f := fun k : ℕ => k) (fun k => Nat.le_mul_of_pos_left k hR) tendsto_id
    have herr := (tendsto_permutationCover_error R).comp htop
    let A : ℝ := Real.logb 2 (4 * (1 + Real.logb 2 R))
    have hupper : Tendsto (fun k : ℕ => Real.logb 2 R +
        (A + Real.logb 2 (R * k : ℕ)) / (R * k : ℕ)) atTop (𝓝 (Real.logb 2 R)) := by
      simpa [A, Function.comp_def] using (tendsto_const_nhds (x := Real.logb 2 R)).add herr
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_logb_card_balancedWords_div_length hR) hupper
    · filter_upwards with k
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hpos k)
        (by exact_mod_cast hlo k)
    · filter_upwards [eventually_gt_atTop 0] with k hk
      have hlen : 0 < (R : ℝ) * (k : ℝ) := by positivity
      have h := permutationCover_logb_le hR (Nat.mul_pos hR hk) (hpos k)
        ((hpos k).trans_le (hlo k)) (card_balancedWords_le R k) (hsize k)
      apply (div_le_iff₀ hlen).mpr
      push_cast at h ⊢
      dsimp only [A]
      field_simp
      linarith

end SpectralBooks
end LinearAlgebra
end OAI
