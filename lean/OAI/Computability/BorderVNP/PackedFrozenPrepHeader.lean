import OAI.Computability.BorderVNP.PackedNamedPortHeaders
import OAI.Computability.BorderVNP.PackedFrozenHistoryCapacity

/-! # Reindexing the native outer port header to the selected epoch's input rectangle -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.Compiled

open Crossing Cover Epoch Epoch.Round Shortening.Adaptive Packing Packing.Inherited Packing.Inherited.WorkWords Packing.Inherited.FrozenTape
open scoped BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m}
    {S : Normalized.SiteSchedule e} {start : ℕ} (t : ℕ)

/-- Reindex a static port table along equality of its actual capacities. -/
def castHeader {n n' : ℕ} (h : n=n') (p : WorkWords.Ports n) : WorkWords.Ports n' :=
  ⟨p.host ∘ Fin.cast h.symm,p.width ∘ Fin.cast h.symm⟩

/-- Reindexing preserves every named attachment and every public width. -/
theorem castHeader_reads {n n' d v : ℕ} {A : Type} {a : A → ℕ} (N : Network d A a)
    (site : N.Site ↪ Fin v) (port : A ↪ Fin n) (h : n=n') (p : WorkWords.Ports n)
    (read : p.Reads N site port) : (castHeader h p).Reads N site (port.trans (finCongr h).toEmbedding) := by
  subst n'; exact read

/-- The named replay's port count agrees with the full port rectangle at the epoch's input. -/
theorem input_port_count :
    portCapacity S (CoverScale.sites (Cube D) start) t = portSlots S start t 0 :=
  path_count S t 0

/-- The machine's actual recursively flattened header presented on the fixed tape's index type. -/
noncomputable def prepHeader (p : WorkWords.Ports (CoverScale.sites (Cube D) start)) : WorkWords.Ports (portSlots S start t 0) :=
  castHeader (input_port_count (S := S) (start := start) t) (p.outer S start t)

end PackedHistoryCircuit.Normalized.SelectedSchedule.Compiled

end BorderVNP
end Computability
end OAI
