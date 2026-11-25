import OAI.Computability.BorderVNP.PackedNamedPortHeaders

/-! # Preserving a grouped exterior-port directory through the minimizing return -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary.Compilation

open Cover Crossing BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Packing Packing.Inherited Packing.Inherited.WorkWords
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 2200000

variable {D m np : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
    {e : PaidIdentity K D m} {S : SiteSchedule e} {shape : ℕ → Shape}
    {start T t w : ℕ} {budget V E cap : ℕ → ℕ}
    {deep : S.floor+1+S.drop*T ≤ start} {ht : t<T} {endShape : shape (t+1) = ⟨V S.rounds,E S.rounds⟩}
    {nodes : ∀ i : Fin S.rounds, S.source.Node S.last (S.high (offset S start t)) V E w S.fanIn i}
    (A : Compilation (bits := bits) deep ht budget V E cap w endShape nodes)
    (c : Fin (fan S) → Admissible (Good (S := S) (start := start) (bits := bits) (shape := shape) (w := w) budget) t)
    (q : A.epoch.F.Hist (A.epoch.run c).flat)
    (p : WorkWords.Ports np) (ports : Port S.fanIn (Port (fan S) P t) S.rounds ↪ Fin np)

local notation3 (prettyPrint := false) "R" => A.returned c
local notation3 (prettyPrint := false) "root" => (R).run.root q

/-- The grouped width and attachment directory of the final named inner state is the
directory of the flattened outer state, with the ports enumerated by their original leaves. -/
theorem widthReturn_ports
    (read : p.Reads (root).val.placed.pack.layout (root).val.names.sites ports) :
    p.Reads (A.epoch.term c q).val.pack.layout (A.epoch.term c q).val.rows.site (Flat.portRows S.rounds ports) := by
  have flat := p.flatten (root).val.placed.pack (root).val.names.sites ports read
  refine ⟨fun z => ?_,flat.size,flat.hole⟩
  exact (flat.attach z).trans ((R).rows_attach q z).symm

end PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary.Compilation

end BorderVNP
end Computability
end OAI
