import OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm.Padding
import OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm.Sorting
import OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm.Spec
import OAI.LinearAlgebra.MatrixExponent.Valued.Shared

/-!
# The sorting protocol with deterministic control

The geometry argument is applied to permutation procedures with
bounded word programs. This avoids deducing deterministic running
time from the size of a network that tests a function's graph.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm
open Coloring Transport
open scoped Classical

variable {F : Type} [Field F]

/-- The groups contain at most 2^(τ h + O(1)) ports. The data width
may be chosen after the exponents, dispatch and group assignment. -/
def SortingProtocol (F : Type) [Field F] : Prop :=
  ∀ τ : ℝ, 0 < τ → ∃ (m : ℕ) (T : Layout F m) (s : Rig T.params) (P : Palette T s) (c D : ℕ),
    2 ≤ m ∧ (∀ h : ℕ, (↑(h / m) : ℝ) ≤ τ * h) ∧ ∀ᶠ h in Filter.atTop, Nonempty (SortingAt T s P c D h)

theorem protocol_of_shared_price [Finite F] (hs : Prices.SharedPrice (AlgebraicClosure F)) :
    SortingProtocol F := by
  intro τ hp
  obtain ⟨m, hm⟩ := exists_nat_gt (max 2 (1 / τ))
  have hd : 2 ≤ m := by exact_mod_cast (le_max_left _ _).trans hm.le
  have hr : 1 ≤ (m : ℝ) * τ := (div_le_iff₀ hp).mp ((le_max_right _ _).trans hm.le)
  obtain ⟨T, hT⟩ := layout_of_shared_price computability hs m (by omega)
  obtain ⟨s, P, c, D, h⟩ := T.sorting hd hT
  refine ⟨m, T, s, P, c, D, hd, ?_, h⟩
  intro j
  have hi : (↑(j / m) : ℝ) * (m : ℝ) ≤ (j : ℝ) := by exact_mod_cast Nat.div_mul_le_self j m
  calc
    _ ≤ (↑(j / m) : ℝ) * ((m : ℝ) * τ) := le_mul_of_one_le_right (by positivity) hr
    _ ≤ τ * j := by rw [← mul_assoc, mul_comm τ]; exact mul_le_mul_of_nonneg_right hi hp.le

theorem protocol_of_saving [Finite F] (hs : omega F < 9 / 4) : SortingProtocol F :=
  protocol_of_shared_price (shared_of_saving hs)

theorem unpadded {A : Type} {h : ℕ} (a : A) (x y : B h → A) (σ : Equiv.Perm (B h)) :
    (∀ i, padded a x i = padded a y (inflate h σ i)) ↔ ∀ i, x i = y (σ i) := by
  have atBase (x : B h → A) (j : B h) : padded a x (lowerHalf h j) = x j :=
    dite_eq_left j.isLt
  constructor
  · intro eq j
    have hh := eq (lowerHalf h j)
    rw [show inflate h σ (lowerHalf h j) = lowerHalf h (σ j) from dite_eq_left j.isLt, atBase, atBase] at hh
    exact hh
  · intro eq i
    unfold inflate
    split
    · rename_i hi
      rw [atBase, padded, dite_eq_left hi]
      exact eq _
    · rename_i hi
      simp only [padded, dite_eq_right hi]

variable {h p w u : ℕ} (S : PaddedSystem F h p w u) (σ : Equiv.Perm (B h))

/-- Invalid selectors contribute zero for all data and may be dropped. -/
theorem permutation_sum {C : ℕ} (ok : S.Correct C) (x y : B h → Fin w → Bool) :
    (if ∀ i, x i = y (σ i) then (1 : F) else 0) =
      ∑ z ∈ legal S σ C, ∑ v : Site h → Channels p u,
        let a := S.dispatch (σ, S.selector.code.symm z)
        S.value a (padded (fun _ => false) x) (padded (fun _ => false) y) v *
          (if Joins (commands a) v then 1 else 0) := by
  let a : Fin w → Bool := fun _ => false
  obtain ⟨bound, sum⟩ := ok σ (padded a x) (padded a y)
  simp only [unpadded] at sum
  refine sum.trans (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro z _ hz
  refine Finset.sum_eq_zero fun v _ => ?_
  have hv : S.value (S.dispatch (σ, S.selector.code.symm z)) (padded a x) (padded a y) v = 0 := by
    by_contra hn
    exact hz (Finset.mem_filter.mpr ⟨Finset.mem_univ _, bound _ v hn⟩)
  exact mul_eq_zero_of_left hv _

end OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm
