import OAI.Hierarchy.DescentInitialHost
import OAI.Hierarchy.CorrectionBatch

namespace OAI
/-! # Initializing native T from the exact public open-network approximation -/

namespace Hierarchy.DescentInitialHost
open ThreeFlat Routing Catalyst
open scoped Classical BigOperators
noncomputable section
variable {F : Type*} [Field F] {k p : ℕ}

/-- Initializing one copy uses the existing trivalent single-bit copy network,
preserves every public coefficient, and explicitly prices every added tether.
The finite simple neighbors include its one new hub at each physical bit. -/
theorem «initialize» (X : Approximation F k p) :
    let N := X.network.copyGraph
    (∀v,(near N v).card≤3) ∧
    Fintype.card (Site N)+Fintype.card (Wire N)+Fintype.card (Port p X.width)≤10*(X.size+1) ∧
    (∀x : Port p X.width → Bool,
      (∑ y : Fin (Fintype.card (Port p X.width))→Fin 1→Bool, ∑ a : N.Assignment,
        (∏ v,N.read X.network.copyTable a y v)*
        (∏ i : Fin (Fintype.card (Port p X.width)),
          if y i=(fun _ => x ((Fintype.equivFin _).symm i)) then 1 else 0))=X.coeff x) := by
  obtain ⟨tri,volume,full⟩ := CorrectionBatch.physical_output X
  dsimp only
  refine ⟨near_le_three _ tri,?_,?_⟩
  · rw [host_card,X.network.copyGraph_bitVolume]
    simp only [Fintype.card_fin,Approximation.size]
    omega
  · intro x
    have result := (with_hubs _ _ (fun i _ => x ((Fintype.equivFin _).symm i))).trans (full x)
    convert result using 2; ext y; simp

end
end Hierarchy.DescentInitialHost

end OAI
