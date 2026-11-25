import OAI.Computability.BorderVNP.PackedInheritedWorkTransport
import OAI.Computability.BorderVNP.PackedInheritedWorkPorts

/-! # Private bank budget and static port headers at the second dense save -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.WorkWords

open Crossing Shortening Cover Epoch Epoch.Round PackedHistoryCircuit.Normalized
open scoped Classical BorderVNP.Epoch.Cube

variable {D lev V E np : ℕ} {P K : Type} {bits : P → ℕ} (p saved : PlacedPack D P bits K (Cube D) lev)
variable (dir : Directory p V E) (names : Directory saved V E) (eq : saved = p.dense dir.cables)

include eq in
/-- Each represented static exterior port still has the same numeric row
and width on the actual saved named state. -/
theorem Ports.Reads.stored (ports : Ports np) (port : P ↪ Fin np) (hn : HEq names dir.dense)
    (h : ports.Reads p.pack.layout dir.sites port) : ports.Reads saved.pack.layout names.sites port := by
  subst saved
  cases eq_of_heq hn
  exact ⟨h.attach,h.size,h.hole⟩

/-- The same tile cap covers the transported true private programs. It
uses the public descriptors and separately charged private work in the
precise finite-port instance of the saved state. -/
theorem bankWithin_stored {fin fin' : Fintype P}
    (programs : @Site.Programs D P fin bits p.pack.layout) (ex : Bool) (bound : ℕ)
    (h : @RecordsWithin D lev P (Cube D) fin _ bits K p (@Site.Programs.bankFields D P fin bits _ programs) ex bound) :
    let installed := carryPrivatePrograms p saved dir.cables eq (fin' := fin') programs
    @RecordsWithin D lev P (Cube D) fin' _ bits K saved (@Site.Programs.bankFields D P fin' bits _ installed) ex bound := by
  cases Subsingleton.elim fin fin'
  subst saved
  intro installed t
  have sorted := @Names.localRecords_denseLayout D E P bits p.pack.layout dir.cables fin ex
    programs.bankFields.prior programs.bankFields.payload (fun v => productAddress lev (p.site v) = t)
  exact (congrArg (1+·) sorted).le.trans (h t)

end Packing.Inherited.WorkWords

end BorderVNP
end Computability
end OAI
