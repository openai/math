import OAI.Computability.BorderVNP.FiniteCandidateSewnRows
import OAI.Computability.BorderVNP.PackedHistorySeedPlan
import OAI.Computability.BorderVNP.PackedHistoryNormalizedGridBirth
import OAI.Computability.BorderVNP.PackedOriginalDescriptionRows
import OAI.Computability.BorderVNP.DiagonalExternalSewEnrichedLayout
import OAI.Computability.BorderVNP.PackedNativeDemandPacket
import OAI.Computability.BorderVNP.DiagonalNumberedTape

/-! # A single signed packet family on the public evaluator histories -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Packing PhysicalEpochs DeckGrid
open Diagonal Diagonal.CellEntries Diagonal.ExternalSew TeamContraction TeamScales Filter EnrichedOuter
open ParseBatch ParseBatchVerifier Prewire VPVNP RoutingOutputs
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxRecDepth 6000
set_option maxHeartbeats 2400000

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m}
    {S : PackedHistoryCircuit.Normalized.SiteSchedule e} {n r d T copies header work R ell : ℕ}
    (plan : SeedPlan S n r d T copies header work)
local notation "axes" => Fintype.card (Cube D)
local notation "tiles" => GridHosts.tileCount axes d
local notation "block" => GridHosts.inputBlockWidth r n axes d
local notation "mass" => initialMass (D := D) n r d copies header
local notation "admit" => Boundary.Good (S:=S) (start:=d+1)
  (bits:= fun _ : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) => copies*GridHosts.inputBlockWidth r n (Fintype.card (Cube D)) d)
  (shape:=boundaryShape S (d+1)) (w:=60*logWidth r n) (boundaryBudget S mass)
local notation "cap" => seedBoxCapacity n r axes d (Fintype.card (Direction axes))
local notation "desc" => seedDescriptionWidth n r axes d (header*logWidth r n) (BottomGridBank.bodyBudget cap)

/-- For each native profile, the physical row table determines the label
scan input and the width of every individual charged row before any pin bits. -/
def SignedLabelRows (count : (fan S)^T*copies = R+1) (ell a : ℕ) (α ξ : ℝ) : Prop :=
  ∀ {t pins inner : ℕ} {Edge : Type} [Fintype Edge] (G : Wiring R r t pins ell inner n Edge),
  G.program.length+t = literal α n →
  ∀ (order : Fin tiles ≃ (Fin axes → Deck (d+2)))
    (pos : (Fin axes → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    {g : ℕ} {len : Fin n} {st : Fin g} (W : WiredWitness G len D axes d order st)
    (tag : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ) {ns ne np : ℕ}
    (sites : (W.routedFine pos).Site ↪ Fin ns) (edges : (W.routedFine pos).Edge ↪ Fin ne)
    (ports : Fin r × Fin (publicWidth G) ↪ Fin np)
    (table : (seedBundle G axes d order pos copies).Tables K)
    (words : Boundary.Pins S (d+1) (boundaryShape S (d+1)) (60*logWidth r n) 0 → Bool)
    (ready : admit 0 (Boundary.seedState S G d order pos copies table words)),
    let dir := freeDirectory R r (G.program.length+t) ell tiles block ((fan S)^T*tiles) desc
    ∃ bounds : dir.DestinationBounds,
    let bottom : Admissible admit 0 := ⟨_,ready⟩
    let M := plan.compiled.machine
    ∀ (q : (packHistory bottom M.epoch T).Index) {cells : ℕ}
      (number : (Cube D → Deck (depth S (d+1) T+1)) ≃ Fin cells),
      let state := ((packHistory bottom M.epoch T).term q).val
      let N := enrichedSewnLayout G axes d order pos count M bottom rfl q
      let cell (v : N.Site) := number (reduceMove (depth S (d+1) T) (state.route.origin v))
      let old := originalDescriptionRows M bottom q dir rfl order
      let live := (Equiv.refl (FreeBlock R tiles)).toEmbedding
      ∀ {ce cp : ℕ} (edge : N.Edge ↪ Fin ce) (port : FreeBlock R tiles ↪ Fin cp) (gap : ℕ),
        let list := NativeDemands.rows N cell edge port dir old live gap
        let recv := NativeDemands.receiver N cell edge port dir old live gap bounds
        BorderVNP.Cube.Physical.PackedLabelBudget N cell recv (fun i : Fin list.length => list[i.val].width)
          ((R+1)*exterior ξ r n : ℕ) (width n (1/4)) (BorderVNP.Cube.labelCount α a n)


variable (count : (fan S)^T*copies = R+1)
    {time pins inner : ℕ} {Edge : Type} [Fintype Edge] (G : Wiring R r time pins ell inner n Edge)
    (order : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2)))
    (pos : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    {g : ℕ} {len : Fin n} {st : Fin g} (W : WiredWitness G len D (Fintype.card (Cube D)) d order st)
    (tag : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ) {ns ne np : ℕ}
    (sites : (W.routedFine pos).Site ↪ Fin ns) (edges : (W.routedFine pos).Edge ↪ Fin ne)
    (ports : Fin r × Fin (publicWidth G) ↪ Fin np)
    (table : (seedBundle G (Fintype.card (Cube D)) d order pos copies).Tables K)
    (words : Boundary.Pins S (d+1) (boundaryShape S (d+1)) (60*logWidth r n) 0 → Bool)
local notation "initialState" => Boundary.seedState S G d order pos copies table words
variable (ready : Boundary.Good (S:=S) (start:=d+1)
    (bits:=fun _ : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) =>
      copies*GridHosts.inputBlockWidth r n (Fintype.card (Cube D)) d)
    (shape:=boundaryShape S (d+1)) (w:=60*logWidth r n)
    (boundaryBudget S (initialMass (D:=D) n r d copies header)) 0
    (Boundary.seedState S G d order pos copies table words))
local notation "bottom" => (Subtype.mk initialState ready : Admissible admit 0)
local notation "M" => plan.compiled.machine
local notation "dir" => freeDirectory R r (G.program.length+time) ell tiles block ((fan S)^T*tiles) desc

variable {F : Type} [Field F] (cube : FixedCube F) (α ξ : ℝ)
    (calibrated : plan.SignedLabelRows count ell (cube.pred+1) α ξ) (lit : G.program.length+time = literal α n)
    (hd : 0 < BorderVNP.Cube.alphabet α n)
    (hp : (fieldSewParams G (Fintype.card (Cube D)) d).Valid)
    {cells : ℕ} (number : (Cube D → Deck (depth S (d+1) T+1)) ≃ Fin cells) (gap : ℕ)
local notation3 (prettyPrint := false) "validRows" => calibrated G lit order pos W tag sites edges ports table words ready
local notation3 (prettyPrint := false) "net" q => enrichedSewnLayout G axes d order pos count M bottom rfl q

/-- The one packet family indexed only by the native public history. On
each history the real geometry assigns the final cells, sorted sparse cable
addresses, immutable description receivers, and native first-minimum teams. -/
noncomputable def signedPackets (q : (packHistory bottom (M).epoch T).Index) :
    PacketPlacement (Port (fan S) (Fin copies × Unit) T) cube.pred (BorderVNP.Cube.alphabet α n)
      cube.b cube.h cube.copies (net q) := by
  let a := ((packHistory bottom (M).epoch T).term q).val
  let cell := fun v : (net q).Site => number (reduceMove (depth S (d+1) T) (a.route.origin v))
  let edge := FieldExport.mergedEdges (fieldSewParams G axes d) hp a.rows.edge
  let port : FreeBlock R tiles ↪ Fin ((R+1)*tiles) := finProdFinEquiv.toEmbedding
  let old := originalDescriptionRows M bottom q dir rfl order
  let live := (Equiv.refl (FreeBlock R tiles)).toEmbedding
  let bounds := (validRows).choose
  have bud := (validRows).choose_spec q number edge port gap
  exact RoutingOutputs.NativeDemands.packet (net q) cell edge port dir old live gap bounds cube
    (SewnTape.teamNumber (fan S) T copies R count).symm hd bud

/-- The common packet count on every signed history uses exactly the fixed
team exterior volume, including when an individual selector has zero weight. -/
theorem signedPackets_blocks (q : (packHistory bottom (M).epoch T).Index) :
    (plan.signedPackets count G order pos W tag sites edges ports table words ready cube α ξ calibrated lit
      hd hp number gap q).blocks =
      BorderVNP.Cube.Physical.blocksFor ((R+1)*exterior ξ r n : ℕ) (cube.h*cube.b)
        ((BorderVNP.Cube.alphabet α n)^(cube.pred+1)) := rfl

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
