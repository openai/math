import OAI.LinearAlgebra.SpectralBooks.PortGraph.PlanarAssemblyIncidence
import OAI.LinearAlgebra.SpectralBooks.PlanarSurgery.PlanarForestEuler

/-! # Euler counts for an assembly of patch forests

A turn and a forest step preserve the occurrence coordinate. Their cycle
counts and the number of moved forest darts therefore sum over the pieces.
Each connected disk contour has one cycle in its occurrence.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
open scoped Classical
open Equiv Equiv.Perm HyperbolicObstruction.PictureSwitch

namespace PortGraph.StubPairing

universe u
variable {J : Type u} {S : J → Type u} [Fintype J] [∀ i, Fintype (S i)]
    (C : StubPairing S) (P : ∀ i, OpenPiece (S i))
    (num : (C.assemble P).Numbering) (t f : ∀ i, Perm (PieceDart P i))
    (ht : ∀ x, C.dartEquiv P (num.turn x) = Equiv.sigmaCongrRight t (C.dartEquiv P x))

include ht in
/-- Each local tree contraction decreases its vertex count once per band.
The global forest accounts for exactly that many pairs of moved darts. -/
theorem assembly_forest_cost
    (hcost : ∀ i, 2 * (cycles (t i) - cycles (t i * f i)) = ((f i).support.card : ℤ)) :
    2 * (cycles num.turn - cycles (num.turn * C.liftPiecePerm P f)) =
      ((C.liftPiecePerm P f).support.card : ℤ) := by
  have h₁ : cycles num.turn = ∑ i, cycles (t i) := by
    simpa only [cycles_eq_card_classes] using cycles_of_piecePerm (C.dartEquiv P) num.turn t ht
  have h₂ : cycles (num.turn * C.liftPiecePerm P f) = ∑ i, cycles (t i * f i) := by
    simpa only [cycles_eq_card_classes] using cycles_of_piecePerm (C.dartEquiv P)
      (num.turn * C.liftPiecePerm P f) _ (C.dartEquiv_turnAfterForest P num t f ht)
  have h₃ : (C.liftPiecePerm P f).support.card = ∑ i, (f i).support.card := by
    convert! support_card_of_piecePerm (C.dartEquiv P) (C.liftPiecePerm P f) f
      (C.dartEquiv_liftPiecePerm P f) using 1
  rw [h₁,h₂,h₃,Nat.cast_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => hcost i

variable (orbit : ∀ i (a b : PieceDart P i), (t i * f i).SameCycle a b)

include ht orbit in
omit [∀ i, Fintype (S i)] in
/-- The cycles after the forest step are exactly the occurrence fibers. -/
theorem assembly_forest_orbit (x y : C.Edge P × Bool) :
    (num.turn * C.liftPiecePerm P f).SameCycle x y ↔ (C.dartEquiv P x).1 = (C.dartEquiv P y).1 :=
  sameCycle_iff_piece (C.dartEquiv P) _ _ (C.dartEquiv_turnAfterForest P num t f ht) orbit x y

include ht orbit in
omit [∀ i, Fintype (S i)] in
/-- When every occurrence has a stub, no occurrence disappears from the
count of disk contours. -/
theorem assembly_forest_cycles (stubs : ∀ i, Nonempty (S i)) :
    cycles (num.turn * C.liftPiecePerm P f) = Fintype.card J := by
  apply cycles_of_classifier _ (fun x => (C.dartEquiv P x).1) (C.assembly_forest_orbit P num t f ht orbit)
  intro i
  exact ⟨C.stubMark P ⟨i,(stubs i).some⟩, congrArg Sigma.fst (C.dartEquiv_stubMark P _)⟩

include ht orbit in
/-- Euler's equation for a spherical assembly with the selected internal
forest and the original pairing of exterior stubs. -/
theorem assembly_forest_euler
    (sub : ∀ i d, f i d = d ∨ f i d = insideMate P i d)
    (hcost : ∀ i, 2 * (cycles (t i) - cycles (t i*f i)) = ((f i).support.card : ℤ))
    (hs : num.rotation.picture.GenusZero) :
    cycles (num.turn * C.liftPiecePerm P f) +
      cycles ((num.turn * C.liftPiecePerm P f) * C.outsidePairing P) -
      ((C.outsidePairing P).support.card : ℤ)/2 =
      2 * (Nat.card (Quotient num.rotation.picture.components) : ℤ) := by
  let M := num.rotation.picture
  have hv : M.vertex = num.turn := num.rotation.picture_vertex
  have cost := C.assembly_forest_cost P num t f ht hcost
  rw [← hv] at cost ⊢
  apply PlanarSurgery.forest_euler_of_fibers M (fun x => (C.dartEquiv P x).1)
    (C.liftPiecePerm P f) (C.outsidePairing P) (C.liftPiecePerm_subpairing P f sub) _ _
    (C.outsidePairing_apply P) _ (by omega) hs
  · intro x
    rw [hv,ht]
    rfl
  · intro x
    rw [C.dartEquiv_liftPiecePerm]
    rfl
  · rw [hv]
    exact C.assembly_forest_orbit P num t f ht orbit

include ht in
/-- When the pieces themselves are trees, the equality on contours is
equivalent to sphericity of the glued numbered map. -/
theorem assembly_inside_euler_iff
    (hcost : ∀ i, 2 * (cycles (t i) - cycles (t i * insideMate P i)) = ((insideMate P i).support.card : ℤ)) :
    (cycles (num.turn * C.liftPiecePerm P (insideMate P)) +
      cycles ((num.turn * C.liftPiecePerm P (insideMate P)) * C.outsidePairing P) -
      ((C.outsidePairing P).support.card : ℤ)/2 =
      2 * (Nat.card (Quotient num.rotation.picture.components) : ℤ)) ↔ num.rotation.picture.GenusZero := by
  let M := num.rotation.picture
  have hv : M.vertex = num.turn := num.rotation.picture_vertex
  have cost := C.assembly_forest_cost P num t (insideMate P) ht hcost
  rw [← hv] at cost ⊢
  apply PlanarSurgery.forest_euler_iff_of_full M _ _
    (C.liftPiecePerm_subpairing P _ fun _ _ => Or.inr rfl) _ (C.inside_mul_outsidePairing P) (by omega)
  rintro ⟨e | e,b⟩
  · left
    apply (C.dartEquiv P).injective
    rw [C.dartEquiv_liftPiecePerm]
    rfl
  · exact Or.inr rfl

end PortGraph.StubPairing

end

end SpectralBooks
end LinearAlgebra
end OAI
