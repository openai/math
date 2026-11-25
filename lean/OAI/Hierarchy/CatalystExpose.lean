import OAI.Hierarchy.CatalystSampleRestriction
import OAI.Hierarchy.GridSum
import OAI.Hierarchy.CorrectionFrame
import OAI.Hierarchy.CorrectionProducts
import OAI.LinearAlgebra.SpectralBooks.SpectralPlacementPrices.ShortenPrice

namespace OAI
/-! # Exposing all tick inputs at their common data site

A pinned row acquires one fixed basis indicator at the origin. This is a
local linear map on the grouped tensor. The ordinary sum has precisely
two choices per data pin, and the common normalization costs at most 2k. -/

noncomputable section
namespace Hierarchy.Catalyst

open LinearAlgebra.SpectralBooks SiteTensor CorrectionFrame
open scoped BigOperators Classical

variable {F : Type*} [Field F] {p k : ℕ} {b : Fin k → ℕ}

private def wireSite : Wire b × Bool → Location k := fun i => some (i.1.1,i.2)

private def sliceTerm (a : Fin p → Bool) (f : (Wire b × Bool → Bool) → F) :
    (Port p b → Bool) → F := fun x =>
  if (fun i => x (.inl i)) = a then f (fun j => x (.inr j)) else 0

set_option maxHeartbeats 1600000 in
/-- Appending an arbitrary number of singleton basis indicators at one site is
a restriction even if the center had no original wires. -/
private theorem slice_restricts (a : Fin p → Bool) (f : (Wire b × Bool → Bool) → F) :
    ((CorrectionProducts.raw (sliceTerm a f)).group location).Restricts
      ((CorrectionProducts.raw f).group wireSite) := by
  classical
  let localInput (j : Location k) := {i : Wire b × Bool // wireSite i = j} → Bool
  let localOutput (j : Location k) := {i : Port p b // location i = j} → Bool
  let project (j : Location k) (x : localOutput j) (i : {t : Wire b × Bool // wireSite t = j}) :=
    x ⟨.inr i.val,i.property⟩
  let agreesAt : (j : Location k) → localOutput j → Prop
    | none, x => (fun i : Fin p => x ⟨.inl i,rfl⟩) = a
    | some _, _ => True
  let reconstruct (x : (j : Location k) → localOutput j) (i : Port p b) :=
    x (location i) ⟨i,rfl⟩
  let ok (x : (j : Location k) → localOutput j) := (fun i : Fin p => reconstruct x (.inl i)) = a
  let src := (CorrectionProducts.raw f).group wireSite
  let dst := (CorrectionProducts.raw (sliceTerm a f)).group location
  apply restriction_of_sample (I:=Location k) (A:=src.Leg) (B:=dst.Leg)
    (F:=F) dst.coeff src.coeff project agreesAt ok
  · intro x
    constructor
    · exact fun h => h none
    · intro yes j
      cases j with
      | none => exact yes
      | some _ => trivial
  · intro x
    rfl

theorem Approximation.expose [NeZero k] (X : Approximation F k p)
    (f : (Fin p → Bool) → F) {D : ℝ} (pointwise : X.PointwiseGap f D) :
    X.Gap f (D-2*k*p) := by
  classical
  let : Nontrivial (Location k) :=
    ⟨⟨none, some (⟨0, Nat.pos_of_ne_zero (NeZero.ne k)⟩,false), by intro h; cases h⟩⟩
  intro P
  let row (a : Fin p → Bool) := (X.pinnedError f a).coeff
  let term (a : Fin p → Bool) := sliceTerm a (row a)
  have total : ∑ a, term a = (X.error f).coeff := by
    funext x
    rw [Finset.sum_apply]
    simp only [term,sliceTerm]
    rw [Finset.sum_ite_eq Finset.univ _]
    simp only [Finset.mem_univ,ite_true]
    exact congrArg (X.error f).coeff (by funext j; cases j <;> rfl)
  by_cases vanish : (X.error f).coeff=0
  · exact Or.inl vanish
  right
  have nz : ∑ a, term a ≠ 0 := total ▸ vanish
  obtain ⟨a,notZero,price⟩ := GridSum.price_sum P (frame k) location term nz
  have nonzero : row a ≠ 0 := by
    intro h
    apply notZero
    show sliceTerm a (row a)=0
    rw [h]
    funext x
    change (if _ then (0 : F) else 0)=0
    exact ite_self _
  obtain zero | bound := pointwise P a
  · exact (nonzero zero).elim
  have single := P.placed_mono (frame k) (slice_restricts a (row a))
  rw [← P.group,← P.group] at single
  have logCount : Real.logb 2 (Fintype.card (Fin p → Bool)) = p := by
    simp [Real.logb_pow]
  rw [logCount] at price
  have scale := mul_le_mul_of_nonneg_right (scale_le P) (Nat.cast_nonneg (α:=ℝ) p)
  rw [sites_eq]
  change P.price (CorrectionProducts.raw (X.error f).coeff) (frame k ∘ location) ≤ _
  rw [← total]
  apply price.trans
  exact (add_le_add (single.trans bound) scale).trans (by linarith)

end Hierarchy.Catalyst
end

end OAI
