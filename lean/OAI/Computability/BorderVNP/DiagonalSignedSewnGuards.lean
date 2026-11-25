import OAI.Computability.BorderVNP.PackedSignedSeedGuards
import OAI.Computability.BorderVNP.PackedBankWiredSeedState
import OAI.Computability.BorderVNP.PackedSewnBirthGuards
import OAI.Computability.BorderVNP.DiagonalEnrichedSewnTagModels
import OAI.Computability.BorderVNP.PackedSelectedPrivateFieldRows

/-! # Private guard invariants on the physically initialized signed grid -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary

open Cover Crossing BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Packing Packing.DeckGrid Packing.PhysicalEpochs
open Diagonal.ExternalSew Diagonal.ExternalSew.RowTrace TeamContraction GridPlacement Shortening.PreparedBins
open ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar Inherited BottomGridBank BottomReports DeckGrid.WiredWitness
open scoped Classical
attribute [local instance] portFintype
set_option maxHeartbeats 2400000

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)
    {R r t pins link inner n g d : ℕ} {Edge : Type} [Fintype Edge] {G : Wiring R r t pins link inner n Edge}
    {len : Fin n} {key : Fin g}
    {order : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2))}
    (W : WiredWitness G len D (Fintype.card (Cube D)) d order key)
    (position : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (tag : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ) {ns ne np : ℕ}
    (siteID : (W.routedFine position).Site ↪ Fin ns) (edgeID : (W.routedFine position).Edge ↪ Fin ne)
    (portID : (Fin r × Fin (publicWidth G)) ↪ Fin np) (copies : ℕ)

/-- Use the routed grid's equality instance in the signed seed incidence directory. -/
noncomputable local instance guardFieldDeckEq {q l : ℕ} : DecidableEq (Fin q → Deck (l+2)) := Classical.decEq _

local notation "axes" => Fintype.card (Cube D)
local notation "tiles" => GridHosts.tileCount (Fintype.card (Cube D)) d
local notation "degree" => Fintype.card (Direction axes)
local notation "K₀" => seedBoxCapacity n r axes d degree
local notation "channels" => Shortening.PublicCapacity.Rows.edge (groupedGridRows G axes d order position copies)
local notation "groups" => Equiv.toEmbedding (Equiv.refl (Fin tiles))
local notation "L₀" => seedBundle G axes d order position copies

variable {w : ℕ} (table : (seedBundle G (Fintype.card (Cube D)) d order position copies).Tables K) (words : Pins S (d+1) (SelectedSchedule.boundary S (d+1)) w 0 → Bool)
local notation "state₀" => seedState S G d order position copies table words

/-- The actual private verifier banks meet the guard hypotheses at every bottom
site in the selected machine's finite enumeration. -/
theorem wiredSeedStatePrograms_guards (U : ℕ) (v : (state₀).pack.layout.Site) :
    let src := wiredSeedStatePrograms S W position tag siteID edgeID portID copies table words v
    src.birth.Local ∧ src.birth.RelativeBoxes ∧
      src.program.CompilerFields e (max (tableLimit e) (max 8 K₀)) U ∧ src.program.SignFree := by
  intro src
  have bottom := W.seedBorn_guard position tag siteID edgeID portID channels groups v copies
  exact ⟨bottom.1,bottom.2,
    W.seedBorn_compilerFields position tag siteID edgeID portID channels groups v e copies _ U
      ((le_max_left ..).trans (le_max_right ..)) ((le_max_right ..).trans (le_max_right ..)),
    W.seedBorn_signFree position tag siteID edgeID portID channels groups v copies⟩

end PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary

namespace PackedHistoryCircuit.Normalized.SelectedSchedule

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Packing Packing.Inherited Packing.DeckGrid Packing.PhysicalEpochs Diagonal Diagonal.ExternalSew
open TeamContraction ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar
open EnrichedOuter Boundary GridHosts
open scoped Classical BigOperators BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 2200000
set_option maxRecDepth 5500
set_option synthInstance.maxSize 4000

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} {S : SiteSchedule e}
    {R r t pins link inner n g d copies T w : ℕ} {Edge : Type} [Fintype Edge] {G : Wiring R r t pins link inner n Edge}
    {len : Fin n} {key : Fin g}
    {order : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2))}
    (W : WiredWitness G len D (Fintype.card (Cube D)) d order key)
    (pos : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (tag : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ) {ns ne np : ℕ}
    (sites : (W.routedFine pos).Site ↪ Fin ns) (edges : (W.routedFine pos).Edge ↪ Fin ne)
    (ports : Fin r × Fin (publicWidth G) ↪ Fin np)
    (table : (seedBundle G (Fintype.card (Cube D)) d order pos copies).Tables K)
    {budget : ℕ → ℕ} {cap : ℕ → ℕ → ℕ} {deep : S.floor+1+S.drop*T ≤ d+1}
    (C : Compiled (fun _ : Fin (tileCount (Fintype.card (Cube D)) d) =>
      copies*inputBlockWidth r n (Fintype.card (Cube D)) d) deep budget cap w)
    (words : Pins S (d+1) (boundary S (d+1)) w 0 → Bool)
    (good : Good budget 0 (seedState S G d order pos copies table words))
    (seeds : ∀ h, ∀ i : Fin S.rounds,
      ((Cube D → Deck (S.level (offset S (d+1) h) (i.val+1)+1)) × (S.source.pattern i).bins.Bin) → ℕ)
    {nc : ℕ} (ids : Fin (tileCount (Fintype.card (Cube D)) d) ↪ Fin nc)
    (number : e.Entry → ℕ)
    (real : Wiring R r t pins link inner n Edge)
    (count : (fan S)^T*copies = R+1)
    (hp : (fieldSewParams real (Fintype.card (Cube D)) d).Valid)
local notation "axes" => Fintype.card (Cube D)
local notation "adm" => Good (S := S) (start := d+1) (P := Fin (tileCount axes d))
  (bits := fun _ => copies*inputBlockWidth r n axes d) (shape := boundary S (d+1)) (w := w) budget
local notation "leaf" => (Subtype.mk (seedState S G d order pos copies table words) good : Admissible adm 0)
local notation "src" => wiredSeedStatePrograms S W pos tag sites edges ports copies table words
local notation "dir" => C.privateSiteRows ids seeds
local notation "lastPorts" => Flat.portRows T (privatePorts S ids T)

variable (placed : (seedState S G d order pos copies table words).pack.layout =
      (wiredGrid real (Fintype.card (Cube D)) d order pos).groupedRepeat
        (fun _ : Fin (tileCount (Fintype.card (Cube D)) d) => inputBlockWidth r n (Fintype.card (Cube D)) d) order copies)

/-- Every field of the true stored-program compiler has its original relative
address and global scalar bounds after exterior sewing. The same scalar bound
can be used for all teams and all vertices of the public execution. -/
theorem signedSewn_compilerFields (U : ℕ) (fits : ∀ z, number z ≤ U)
    (q : (packHistory (Subtype.mk (seedState S G d order pos copies table words) good) C.machine.epoch T).Index) (v : (enrichedSewnLayout real axes d order pos count C.machine leaf placed q).Site) :
    let L := enrichedSewnPrograms real axes d order pos count C.machine leaf placed lastPorts hp q
      (C.machine.terminalPrivatePrograms dir number leaf src q) v
    L.program.CompilerFields e
      (max (tableLimit e) (max 8 (seedBoxCapacity n r axes d (Fintype.card (Direction axes))))) U := by
  have initial := wiredSeedStatePrograms_guards S W pos tag sites edges ports copies table words U
  have bound := C.machine.historyPrivatePrograms_compilerFields dir number leaf src (le_max_left ..) fits
    (fun u => (initial u).2.2.1) T le_rfl q v
  exact SewnField.stage_compilerFields e _ _ _ _ _ bound

/-- At each genuine sewn vertex the native guard reads its finite bank with
the original relative box addresses. Copy/zero wiring preserves the positive
sign and the stored private width and row format. -/
theorem signedSewn_wellFormed (q : (packHistory (Subtype.mk (seedState S G d order pos copies table words) good) C.machine.epoch T).Index)
    (v : (enrichedSewnLayout real axes d order pos count C.machine leaf placed q).Site) :
    let L := enrichedSewnPrograms real axes d order pos count C.machine leaf placed lastPorts hp q
      (C.machine.terminalPrivatePrograms dir number leaf src q) v
    L.birth.Local ∧ L.program.Schema ∧ L.program.RelativeBoxes ∧ L.program.SignFree := by
  let U := Finset.univ.sup number
  have fits (z) : number z ≤ U := Finset.le_sup (Finset.mem_univ z)
  let site := C.machine.terminal_sewn_guard dir number leaf src q (le_max_left ..) fits
    (wiredSeedStatePrograms_guards S W pos tag sites edges ports copies table words U) v
  exact site _ _

end PackedHistoryCircuit.Normalized.SelectedSchedule

end BorderVNP
end Computability
end OAI
