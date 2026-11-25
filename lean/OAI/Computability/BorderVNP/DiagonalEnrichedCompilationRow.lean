import OAI.Computability.BorderVNP.DiagonalEnrichedNamedRowStep
import OAI.Computability.BorderVNP.DiagonalOriginalRowTree
import OAI.Computability.BorderVNP.PackedHistoryNormalizedCompilation

/-! # Numeric port rows across the actual compiled site epoch -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.RowTrace

open Crossing Cover Epoch Epoch.Round Shortening Adaptive Packing Shortening.PublicCapacity
open PackedHistoryCircuit PackedHistoryCircuit.Normalized EnrichedOuter
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

variable {D m start T t : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
    {e : PaidIdentity K D m} {S : Normalized.SiteSchedule e} {shape : ℕ → Shape} {V E cap budget : ℕ → ℕ} {w : ℕ}
    {deep : S.floor+1+S.drop*T ≤ start} {ht : t<T}
    {endShape : shape (t+1) = ⟨V S.rounds,E S.rounds⟩}
    {nodes : ∀ j : Fin S.rounds, S.source.Node S.last (S.high (offset S start t)) V E w S.fanIn j}
    (A : Boundary.Compilation (bits := bits) deep ht budget V E cap w endShape nodes)
    (c : Fin (fan S) → Admissible (Boundary.Good (S := S) (start := start) (bits := bits)
      (shape := shape) (w := w) budget) t)

set_option maxHeartbeats 1800000 in
/-- Reading the host row from the actual post-frame directory gives the
incoming child's row plus its static offsets through the inner rectangles.
The digits and rectangle sizes are independent of the chosen histogram. -/
theorem compiledEpoch_row (q : A.program.program.Hist ((A.returned c).run.flat))
    (i : Fin (fan S)) (p : Port (fan S) P t) :
    ((A.epoch.term c q).val.rows.site ((A.epoch.term c q).val.pack.layout.attach (i,p))).val =
      flatOffset (fun j (a : Fin S.fanIn) => a.val*V j) S.rounds i +
        ((c i).val.rows.site ((c i).val.pack.layout.attach p)).val := by
  let returned := A.returned c
  let F := A.program.program
  let stride := fun j (a : Fin S.fanIn) => a.val*V j
  let read (j : ℕ) (a : Boundary.Inner S start t V E cap w P bits j) (p : Port S.fanIn (Port (fan S) P t) j) :=
    (a.val.names.sites (a.val.placed.pack.layout.attach p)).val
  have advance (j : ℕ) (hj : j < S.rounds) (child : Fin S.fanIn → Boundary.Inner S start t V E cap w P bits j)
      (hist : (F.system.choose j hj child).Index) (a : Fin S.fanIn) (port : Port S.fanIn (Port (fan S) P t) j) :
      read (j+1) ((F.system.choose j hj child).term hist) (a,port) = stride j a + read j (child a) port :=
    namedSuccessor_row A.program ⟨j,hj⟩ child hist a port
  have inside := assignedRows_flat F.system stride read advance S.rounds le_rfl returned.run.flat q (i,p)
  have leaf : read 0 (returned.run.flat i) p = ((c i).val.rows.site ((c i).val.pack.layout.attach p)).val :=
    (congrArg (fun a => read 0 (a i) p) returned.leaves).trans ((A.input c).originalSiteRow i p)
  exact (returned.rows_attach q (i,p)).trans (inside.trans (congrArg (flatOffset stride S.rounds i + ·) leaf))

end Diagonal.ExternalSew.RowTrace

end BorderVNP
end Computability
end OAI
