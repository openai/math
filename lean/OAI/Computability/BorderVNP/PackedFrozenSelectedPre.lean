import OAI.Computability.BorderVNP.PackedFrozenPrepBatch
import OAI.Computability.BorderVNP.PackedFrozenSelectedSchemas
import OAI.Computability.BorderVNP.PackedInheritedWorkPrep

/-! # The actual width and frozen-record pre-frame of the selected outer machine -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.Compiled

open Crossing Cover Cover.AddressCircuit Epoch Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Shortening.PublicEndpoints Packing Inherited WorkWords FrozenTape EnrichedOuter
open VPVNP.VerifierNetwork
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

variable {D m : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
    {e : PaidIdentity K D m} {S : Normalized.SiteSchedule e} {start T w : ℕ}
    {deep : S.floor+1+S.drop*T ≤ start} {budget : ℕ → ℕ} {cap : ℕ → ℕ → ℕ}
    (C : Compiled bits deep budget cap w) (base : FrozenTape.Format) (t : ℕ) (ht : t<T)
local notation3 "shape₀" => boundaryShape S start t
local notation3 "Fmt" => ProgramSchemas.epoch S start w base t
local notation3 "new" => before S start t 0
local notation3 "leafB" => ProductSlots (Fintype.card (Cube D)) (S.level (offset S start t) 0+1) ⊕ ↥(S.source.catalog 0)
local notation3 "old" => Boundary.Pins S start (boundaryShape S start) w t
local notation3 "A" => ProductSlots (Fintype.card (Cube D)) (depth S start t+1)
local notation3 (prettyPrint := false) "widths" => (C.atLevel t ht).widthPre
variable (ports : WorkWords.Ports (portSlots S start t 0)) (fit : (before S start t 0).sites ≤ 2^w)

/-- The old route's raw endpoint pins, shared by all child tapes. -/
def priorEndpoints (j : Inputs A (shape₀).sites (shape₀).edges w w) : old := .inr (.inr j)

/-- Compute all subdivided endpoint fields, inherited and fresh records, and work widths on
the same complete tuple of actual outer children. -/
noncomputable def tapePre :
    Frame (Fin (fan S) × ProgramSchemas.outerPins S start w base t)
      (Fin (fan S) × ProgramSchemas.stagePins S start w base t 0) :=
  PrepBatch.batch (s := shape₀) (extra := interiors S) (B := leafB) Fmt (priorEndpoints (S := S) (start := start) (w := w) t)
    ports fit ((widths) rfl ports fit)

/-- Explicit cost of the batch, charged to the original geometric subdivision once.
Each leaf contributes its width directory and its actual old-tape lookup and fresh record rows. -/
theorem tapePre_size : (tapePre C base t ht ports fit).size ≤ (C.atLevel t ht).pre.size +
    4 + fan S * Prep.charge (new).sites (new).edges (portSlots S start t 0) w +
    ∑ i : Fin (fan S), PrepBatch.leafCharge (B := leafB) (s := shape₀) (extra := interiors S) Fmt
      (priorEndpoints (S := S) (start := start) (w := w) t) ports fit i := by
  have batch := PrepBatch.batch_size (s := shape₀) (extra := interiors S) (B := leafB) Fmt
    (priorEndpoints (S := S) (start := start) (w := w) t) ports fit ((widths) rfl ports fit)
  have pre := (C.atLevel t ht).widthPre_size (hv := rfl) ports fit
  let charge := fan S * Prep.charge (new).sites (new).edges (portSlots S start t 0) w
  let leaves := ∑ i : Fin (fan S), PrepBatch.leafCharge (B := leafB) (s := shape₀) (extra := interiors S) Fmt
    (priorEndpoints (S := S) (start := start) (w := w) t) ports fit i
  have prep : ((widths) rfl ports fit).size ≤ (C.atLevel t ht).pre.size+1+charge := pre
  have combined : (tapePre C base t ht ports fit).size ≤ ((widths) rfl ports fit).size+3+leaves := batch
  change _ ≤ (C.atLevel t ht).pre.size+4+charge+leaves
  exact combined.trans ((Nat.add_le_add_right (Nat.add_le_add_right prep 3) leaves).trans (by omega))

variable (x : Fin (fan S) × ProgramSchemas.outerPins S start w base t → Bool)

/-- Both augmented geometry columns come from the very same true width-bearing pre-frame. -/
theorem tapePre_width (i : Fin (fan S)) (j : WithWidths
    (S.source.StatePins S.last (S.high (offset S start t)) (fun z => (before S start t z).sites)
      (fun z => (before S start t z).edges) w 0) (new).sites w) :
    (tapePre C base t ht ports fit).eval x (i,.inl j) =
      ((widths) rfl ports fit).eval (fun z => x (z.1,.inl z.2)) (i,j) :=
  PrepBatch.batch_geo (s := shape₀) (extra := interiors S) (B := leafB) Fmt
    (priorEndpoints (S := S) (start := start) (w := w) t) ports fit ((widths) rfl ports fit) x i j

end PackedHistoryCircuit.Normalized.SelectedSchedule.Compiled

end BorderVNP
end Computability
end OAI
