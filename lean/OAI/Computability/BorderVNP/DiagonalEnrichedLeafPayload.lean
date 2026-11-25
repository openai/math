import OAI.Computability.BorderVNP.DiagonalPayloadBound
import OAI.Computability.BorderVNP.DiagonalEnrichedDenseSiteReplay
import OAI.Computability.BorderVNP.PackedEnrichedEpochRecords

/-! # Scalar counts on the equality subdivisions actually installed by an enriched epoch -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries

open Crossing Shortening Cover Epoch Epoch.Round Adaptive Packing
open private sameStorage from OAI.Computability.BorderVNP.DiagonalSiteExecution

variable {D k exp : ℕ} {Team Param Gadget P : Type} [Fintype Team] [Fintype Param] {bits : P → ℕ}

/-- Cast both a tagged site and its actual record fields along the same equality
of layouts. The scalar charge is unchanged at the corresponding physical box. -/
theorem PayloadBound.sameLayout {α : Type*} (net : α → Network D P bits) {a b : α} (eq : a = b)
    (t : Tracked Team Param Gadget exp (net a)) (data : RecordData (net a))
    (h : PayloadBound t.tags data.payload) :
    PayloadBound ((sameStorage (congrArg net eq)).tracked t).tags
      (cast (congrArg (fun a => RecordData (net a)) eq) data).payload := by
  subst b
  exact h.stored (Storage.id _)

/-- The old site factors keep their own scalar payload. Every new equality
site has value zero or one and therefore carries zero scalar occurrences. -/
theorem PayloadBound.subdivision {N : Network D P bits} (t : Tracked Team Param Gadget exp N)
    (routes : N.WireRoutes) (data : RecordData N) (h : PayloadBound t.tags data.payload) :
    PayloadBound (t.subdivide routes).tags (Sum.elim data.payload (fun _ => 0)) := by
  classical
  intro v z x g
  rcases v with old | new
  · exact h old _ _ g
  · change (counters (if _ then 1 else (0 : Entry Param Gadget))).2 g ≤ 0
    split <;> rfl

namespace EnrichedSiteReplay

open PackedHistoryCircuit.Normalized

universe u

variable {m d : ℕ} [NeZero D] {K : Type} [Field K] [Fintype P]
  {e : PaidIdentity K D m} {S : PackedHistoryCircuit.Normalized.SiteSchedule e}
  {A : ℕ → Type u} {view : S.GeometricView d P bits A} {F : S.EnrichedProgram d view}
  {input : Fin (S.fanIn^S.rounds) → Pack D P bits K}
  {route : ∀ i, SiteRoutes (input i) (Cube D) (S.high d) S.budget}
  (run : PackedHistoryCircuit.Normalized.SiteSchedule.EnrichedExecution F input route)

/-- The conditioned tag table and payload map travel through precisely the
same original-pack equality, geodesic equality subdivision and leaf-state save. -/
theorem installed_payloadBound (fields : ∀ i, RecordData (input i).layout)
    (i : Fin (S.fanIn^S.rounds)) (t : Tracked Team Param Gadget exp (input i).layout)
    (h : PayloadBound t.tags (fields i).payload) :
    PayloadBound (installed run i t).tags ((run.initialSites i).installedData (run.inputFields fields i)).payload := by
  let d := run.initialSites i
  let moved := (sameStorage (congrArg Pack.layout (run.originalPack i).symm)).tracked t
  let r := d.routes.routes S.radius
  have original := h.sameLayout (fun p : Pack D P bits K => p.layout) (run.originalPack i).symm t (fields i)
  have subdiv := original.subdivision moved r (run.inputFields fields i)
  let data : RecordData (d.pack.layout.subdivide r) :=
    ⟨Sum.elim (run.inputFields fields i).prior (fun _ => 0),Sum.elim (run.inputFields fields i).payload (fun _ => 0)⟩
  exact subdiv.sameLayout (fun p => p.pack.layout) d.realizes.symm (moved.subdivide r) data

end EnrichedSiteReplay
end Diagonal.CellEntries

end BorderVNP
end Computability
end OAI
