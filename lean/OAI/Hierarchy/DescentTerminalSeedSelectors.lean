import OAI.Hierarchy.DescentSeedChoiceBits
import OAI.Hierarchy.DescentSeedRawBallot
import OAI.Hierarchy.DescentSeedRootHeader

namespace OAI
/-! # Exact bit selectors and old-site scalar weights at the actual copy-network input -/
namespace Hierarchy.DescentSeedRoot
open Hierarchy.DescentInitialHost DescentSixParty Computability.BorderVNP.Crossing
open ThreeFlat Routing Catalyst Diagonal
open Computability.VPVNP.BurstRAM
open scoped BigOperators Classical
noncomputable section

variable {F : Type} [Field F] {k p : ℕ} (X : Approximation F k p) {R s w : ℕ}

private theorem prod_vertices {V H : Type} [Fintype V] [Fintype H] (sites : Fintype (V⊕H))
    (f : V⊕H → F) :
    (∏ u ∈ @Finset.univ _ sites, f u) = (∏ v, f (.inl v)) * ∏ h, f (.inr h) := by
  rw [Subsingleton.elim sites (instFintypeSum V H)]
  exact Fintype.prod_sum_type f

theorem original_weight (c : (initialGroup X R s).Choice) :
    (initialGroup X R s).weight c=∏q : CountKey X R,(originalScalar X q)^(selected X c q) := by
  change (∏j,∏u,Histories.seedFactor _ s u
    (Sum.elim (fun _=>true) (fun _=>false) u) (c j u))=_
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro j _
  let row (u : Old X ⊕ Fin (Fintype.card (Port p X.width))) : F :=
    Histories.seedFactor (markedInput X) s u (Sum.elim (fun _=>true) (fun _=>false) u) (c j u)
  refine (prod_vertices (inferInstance : Fintype (markedInput X).graph.Site) row).trans ?_
  rw [Fintype.prod_sigma]
  simp only [row,Sum.elim_inl,Sum.elim_inr,Histories.seedFactor,Finset.prod_const_one,mul_one]
  apply Finset.prod_congr rfl
  intro v _
  simpa [originalScalar,selected,counter] using public_scalar X c j v

end
end Hierarchy.DescentSeedRoot

end OAI
