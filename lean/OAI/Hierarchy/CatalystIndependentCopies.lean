import OAI.Hierarchy.CatalystSubstitutionCopiesNetwork
import OAI.Hierarchy.CorrectionProductGap
import OAI.Hierarchy.CorrectionBenchmark
import OAI.Hierarchy.GridPriceReindex

namespace OAI
/-! # Independent copies with their exposed, pointwise error gap -/

noncomputable section
namespace Hierarchy.CorrectionBatch
open Catalyst CatalystSubstitution CorrectionFrame CorrectionProducts
open LinearAlgebra.SpectralBooks
open scoped Classical BigOperators
variable {F : Type*} [Field F] {k p : ℕ}

/-- The physically disjoint copies, renumbered inside each catalyst direction. -/
abbrev independentCopies (d : ℕ) (X : Approximation F k p) := copies d X

omit [Field F] in
theorem independentCopies_size (d : ℕ) (X : Approximation F k p) :
    (independentCopies d X).size = d*X.size := copies_size d X

private theorem aux_price (Q : SpectralPlacementPrices F (EuclideanSpace ℝ (Fin k)))
    (b : Fin k → ℕ) (v : (Wire b × Bool → Bool) → F) :
    Q.price (raw v) (fun j => sites (p:=p) b (.inr j)) ≤ 2*(∑ j, (b j : ℝ)) := by
  let x := fun j => sites (p:=p) b (.inr j)
  have bound := Q.transport (raw v) x (fun _ => 0)
  rw [Q.collapsed,Real.dist_eq,sub_zero] at bound
  apply (le_abs_self _).trans (bound.trans ?_)
  have len (j : Wire b × Bool) : dist (x j) 0 = 1 := by
    rcases j with ⟨⟨j,t⟩,s⟩
    cases s <;> simp [x,sites,dist_zero_right]
  change (∑ j : Wire b × Bool, dist (x j) 0 * Real.logb 2 (Fintype.card Bool)) ≤ _
  simp only [len,Fintype.card_bool,Nat.cast_ofNat,Real.logb_self_eq_one (by norm_num : (1:ℝ)<2),
    mul_one,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,Fintype.card_prod,
    Fintype.card_bool,Nat.cast_mul,Nat.cast_ofNat,CorrectionBenchmark.card_wires]; linarith

/-- Independent tensor powers retain the pointwise gap with a loss of at most
two units per axis per copy. The data of different rows may be pinned differently. -/
theorem independentCopies_gap (d : ℕ) (X : Approximation F k p) (f : (Fin p → Bool) → F)
    {D : ℝ} (hk : 0 < k) (hD : 0 ≤ D) (gap : X.PointwiseGap f D) :
    (independentCopies d X).PointwiseGap (dataProduct d f) (D-2*k*d) := by
  intro Q pin
  let : NeZero k := ⟨hk.ne'⟩
  let t (i : Fin d) (j : Fin p) := pin (finProdFinEquiv (i,j))
  let a (i : Fin d) (x : Wire X.width × Bool → Bool) := X.coeff (Sum.elim (t i) x)
  let b (i : Fin d) (x : Wire X.width × Bool → Bool) := ideal X.width f (Sum.elim (t i) x)
  let B := 2 * ∑ j, (X.width j : ℝ)
  let σ (u : Wire X.width × Bool) := location (p:=p) (b:=X.width) (.inr u)
  let e := copiesWirePorts d X.width
  let pos (u : Wire (copiesWidth d X.width) × Bool) := sites (p:=d*p) (copiesWidth d X.width) (.inr u)
  let error := ((independentCopies d X).pinnedError (dataProduct d f) pin).coeff
  have packed : error = fun z => (rows a-rows b) (z ∘ e) :=
    funext fun z => copies_pinned d X f pin z
  have aligned : pos ∘ e = frame k ∘ (σ ∘ Prod.snd) := by
    funext i
    exact congrArg (frame k) (copiesWirePorts_location (p:=p) X.width i)
  change error = 0 ∨ Q.price (raw error) pos ≤ _
  by_cases nz : rows a-rows b = 0
  · exact Or.inl (by rw [packed,nz]; rfl)
  right
  rw [packed,GridLens.raw_price_reindex Q e (rows a-rows b) pos,aligned]
  have exactSite : (fun u : Wire X.width × Bool => sites (p:=p) X.width (.inr u)) = frame k ∘ σ := by
    rw [sites_eq]; rfl
  have base (i : Fin d) : Q.price (raw (b i)) (frame k ∘ σ) ≤ B := by
    rw [← exactSite]
    exact aux_price (p:=p) Q X.width (b i)
  have err (i : Fin d) (nei : a i-b i ≠ 0) :
      Q.price (raw (a i-b i)) (frame k ∘ σ) ≤ B-D := by
    rw [← exactSite]
    exact (gap Q (t i)).resolve_left nei
  have paid := rows_error_price Q (frame k) σ a b hD (scale_le Q) base err nz
  have width : 2 * (∑ j, ((copiesWidth d X.width j : ℕ) : ℝ)) = d*B := by
    simp only [copiesWidth, Nat.cast_mul, ← Finset.mul_sum, B]; ring
  change _ ≤ 2*(∑ j, ((copiesWidth d X.width j : ℕ):ℝ)) - _
  rw [width]
  linarith

end Hierarchy.CorrectionBatch

end
end OAI
