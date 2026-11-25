import OAI.Hierarchy.DescentAtomSchedule
import OAI.Hierarchy.DescentInitialInvoice
import OAI.Hierarchy.DescentSeedWorld

namespace OAI
/-! # Initializing the retained-history reserve from the actual census -/

namespace Hierarchy.DescentInitialHost
open DescentCompiler DescentSixParty Computability.BorderVNP.Crossing Catalyst CatalystSubstitution CorrectionBatch
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F] {k p : ℕ} (X : Approximation F k p) (S : AtomSchedule)
variable {s : ℕ} (c : (initialGroup X S.copies s).Choice)
local notation "N" => X.network.copyGraph

/-- There is one record at each true internal source site on every copy, and none at
the added public hubs. The same population initializes the evolving prefix bound. -/
theorem seed_atom_ledger (positive : 0<S.height) {hist : ℕ} (hh : 0<hist)
    (positions : Fintype.card (Site N)≤S.initialSites) :
    (1/((hist:ℝ)*(S.epochPower:ℝ)^S.priceExponent))*hist*((S.copies*Fintype.card X.network.copyGraph.Site:ℕ):ℝ)≤
      ((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower ∧
      S.Within 0 (∑v,(seedRecords X c v).length) := by
  have old : Fintype.card X.network.copyGraph.Site≤Fintype.card (Site N) :=
    Fintype.card_le_of_injective (fun u : X.network.copyGraph.Site=>(Sum.inl u : Site N)) Sum.inl_injective
  have init := S.initial (old.trans positions) (atoms:=S.copies*Fintype.card X.network.copyGraph.Site) rfl
  exact ⟨S.paid positive hh (Nat.zero_le _) init,(seed_record_total X c).symm ▸ init⟩

theorem seed_atom_host (size : 10*(X.size+1)≤S.initialSites) : Fintype.card (Site N)≤S.initialSites :=
  (initial_sites_le X).trans size

end
end Hierarchy.DescentInitialHost

end OAI
