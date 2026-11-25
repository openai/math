import OAI.Computability.BorderVNP.PackedBankCompiledScalars
import OAI.Computability.BorderVNP.PackedBankWiredSeedState
import OAI.Computability.BorderVNP.DiagonalEnrichedSewnTagModels
import OAI.Computability.BorderVNP.FiniteSewnFieldScalarBounds
import OAI.Computability.BorderVNP.PackedSelectedPrivateFieldRows

/-! # Marked numeric operands in the signed private program arriving at each cell -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField

open Crossing Inherited Diagonal.ExternalSew Diagonal.CellEntries
open scoped Classical

variable {D ae ap be bp : ℕ} {A P U Free Cable : Type}
    [Fintype A] [Fintype P] [Fintype U] [Fintype Cable]
    {width : A → ℕ} (N : Network D A width) (lane : P ↪ Σ a, Fin (width a))
    {cw : Cable → ℕ} (B : Bundle (FineView.layout N lane) Free Cable cw)
    (gw : U → ℕ) (freeLane : Free ↪ Σ u, Fin (gw u)) (owner : U → N.Site)
    (aligned : ∀ f, owner (freeLane f).1 = B.layout.attach f)
    (oldEdge : N.Edge ↪ Fin ae) (oldPort : A ↪ Fin ap)
    (edge : (N.Edge ⊕ Cable) ↪ Fin be) (port : U ↪ Fin bp) (progs : Site.Programs N)

local notation "out" => Network.packExternal (Bundle.layout B) gw owner
local notation "read₀" => sewnRead N lane B gw freeLane owner aligned oldEdge oldPort edge port

/-- Old numeric operands keep their values. Each added interval refers to
an address bounded by the new physical site's extent. -/
theorem sewnPrograms_marked (v : N.Site) (bound : ℕ) (old : (progs v).program.ScalarBound bound) :
    let pr := sewnPrograms N lane B gw freeLane owner aligned oldEdge oldPort edge port progs v
    pr.program.ScalarBound (max bound (max 1 pr.program.size)) := by
  let read := read₀ v ∘ Fin.cast (progs v).size
  exact stage_scalarBound (progs v).program old (intervals read) read (intervals_cover read)

end Packing.SewnField

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

/-- The marked coordinates of every actual staged descriptor are bounded by the
propagated bank mass and the local sewn extent. The original fields are those
of the same physical seed replayed by the fixed selected machine. -/
theorem signedSewn_markedWords (hm : 0 < m) (mass : ℕ) (seed : SiteCap (seedState S G d order pos copies table words).route (wiredSeedStatePrograms S W pos tag sites edges ports copies table words).bankFields true mass)
    (q : (packHistory (Subtype.mk (seedState S G d order pos copies table words) good) C.machine.epoch T).Index) (v : ((packHistory leaf C.machine.epoch T).term q).val.pack.layout.Site) :
    let degree := Fintype.card (Direction axes)
    let cap₀ := seedBoxCapacity n r axes d degree
    let coeff := (birthWordCoefficient e+8)*(BankCharges.bound e+1)*(S.populationFactor+2)
    let bound := max (max 2 (max copies cap₀)) (coeff*(S.publicProgramFactor^T*mass+1))
    let pr := enrichedSewnPrograms real axes d order pos count C.machine leaf placed lastPorts hp q
      (C.machine.terminalPrivatePrograms dir number leaf src q) v
    pr.program.ScalarBound (max bound (max 1 pr.program.size)) := by
  intro degree cap₀ coeff bound pr
  have start := (wiredSeedStatePrograms_bounds S W pos tag sites edges ports copies table words 0).2.2
  have old := C.terminalPrivatePrograms_localScalars_of_extent ids seeds number leaf src hm mass (max 2 (max copies cap₀))
    seed start q v
  let state := ((packHistory leaf C.machine.epoch T).term q).val
  let network := (flattenPack T state.pack).layout
  let h := enrichedBlockHosts real axes d order pos count C.machine leaf placed q
  let tiles := tileCount axes d
  let block := inputBlockWidth r n axes d
  let room := gridRoom real (show 0<tiles from Fintype.card_pos)
  let lane := groupedLane real tiles Fintype.card_pos ((fan S)^T) copies count
  exact SewnField.sewnPrograms_marked network lane h.bundle (fun _ : FreeBlock R tiles => block)
    (freeLane hp.block room) h.groupOwner (h.groupAligned hp.block room) state.rows.edge lastPorts
    (FieldExport.mergedEdges (fieldSewParams real axes d) hp state.rows.edge) finProdFinEquiv.toEmbedding
    (C.machine.terminalPrivatePrograms dir number leaf src q) v bound old

end PackedHistoryCircuit.Normalized.SelectedSchedule

end BorderVNP
end Computability
end OAI
