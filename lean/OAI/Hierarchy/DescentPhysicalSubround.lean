import OAI.Hierarchy.DescentNetworkWorld
import OAI.Hierarchy.DescentGadgetEvaluation
import OAI.Hierarchy.DescentMergedCableCost
import OAI.Hierarchy.DescentNetworkStep

namespace OAI
/-! # A complete selected wire-saving subround as a sum of actual physical graphs -/

namespace Hierarchy.DescentSixParty
open Computability.VPVNP Computability.VPVNP.WireTensor Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {F : Type*} [Field F] {D : ℕ} {P : Type*} {bits : P → ℕ}
variable {I C : Type} [Fintype I]

/-- All output branches have real finite sites and surviving cables. Summing
them restores the full incoming tensor. Both the real edge-width bill and the
site count refer to each same branch that participates in the identity. -/
theorem PoweredGadget.physical_subround (G : PoweredGadget F) (A : World F D P bits)
    (pick : I × Fin 2 ↪ A.graph.Edge) (z : I → ℕ) (hz : ∀i,0<z i)
    (fit : ∀i s,A.graph.width (pick (i,s))=z i*G.b) (oldPack : A.graph.Site → C) :
    ∃ branch : (I → Profile G.C) → World F D P bits,
      (∀x,A.value x=∑ p,(branch p).value x) ∧
      (∀p,Fintype.card (branch p).graph.Site≤Fintype.card A.graph.Site) ∧
      (∀p,((branch p).coreWidth:ℝ)+2*(G.b:ℝ)*(∑i,z i:ℕ) ≤
        (A.coreWidth:ℝ)+G.rate*(G.b*(∑i,z i):ℕ)) := by
  obtain ⟨layout,L,paid,step⟩ := G.network_step A.graph A.tables pick z hz fit
  let sw (p : I→Profile G.C) (i : I) (e : Fin 8) := z i*(((p i).1 e).val+G.k)
  let N (p : I→Profile G.C) := GadgetNetwork.physical A.graph pick (sw p)
  let loc (p : I→Profile G.C) := newSite A.graph pick (layout p) oldPack
  let pos (p : I→Profile G.C) (_ : Merged A.graph pick (layout p) oldPack) : EuclideanSpace ℝ (Fin D) := 0
  have ball (p : I→Profile G.C) (v) : ‖pos p v‖≤1 := by simp [pos]
  let T (p : I→Profile G.C) : (N p).Tables F :=
    GadgetNetwork.tables A.graph pick (sw p) (fun i => z i*G.b) fit A.tables (fun i => L i (p i))
  let out (p : I→Profile G.C) : World F D P bits :=
    ⟨DescentNetworkPartition.quotient (N p) (loc p) (pos p) (ball p),
      DescentNetworkPartition.tables (N p) (loc p) (pos p) (ball p) (T p)⟩
  refine ⟨out,?_,?_,?_⟩
  · intro x
    apply (step x).trans
    apply Finset.sum_congr rfl
    intro p _
    exact (GadgetNetwork.physical_value_eq_grouped A.graph pick (sw p) (fun i => z i*G.b) fit
      A.tables (fun i => L i (p i)) (layout p) x).symm.trans
      (DescentNetworkPartition.value_eq (N p) (loc p) (pos p) (ball p) (T p) x).symm
  · intro p
    exact GadgetNetwork.merged_sites_le A.graph pick (sw p) (layout p) oldPack (pos p) (ball p)
  · intro p
    have ints := GadgetNetwork.merged_width_paid A.graph pick (sw p) (layout p) oldPack (pos p)
      (ball p) G.b z fit
    have reals : ((out p).coreWidth:ℝ)+2*(G.b:ℝ)*(∑i,z i:ℕ)≤
        (A.coreWidth:ℝ)+(surviving (sw p) (layout p):ℝ) := by exact_mod_cast ints
    exact reals.trans (add_le_add (le_refl (A.coreWidth : ℝ)) (paid p))

end
end Hierarchy.DescentSixParty

end OAI
