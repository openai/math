import OAI.Computability.BorderVNP.DiagonalNumberedEnrichedTape
import OAI.Computability.BorderVNP.DiagonalNativeMeanPaths
import OAI.Computability.BorderVNP.PackedBottomWiredSite
import OAI.Computability.BorderVNP.DiagonalPinnedGuards

/-! # Original verifier choices on a fixed accepted public history

The positive program first chooses one shared history. Within its fiber the
guarded integer cell assignments are equivalent to the actual summands of the
numbered expansion. The raw field values do not affect this equivalence. -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries.EnrichedTape

open Crossing Shortening Adaptive Packing Packing.DeckGrid Cover TeamContraction ExternalSew GridHosts
open PackedHistoryCircuit PackedHistoryCircuit.Normalized PublicCapacity VPVNP BorderVNP.Cube MvPolynomial
open scoped BigOperators Classical BorderVNP.Epoch.Cube

universe u

variable {D m start T : ℕ} [NeZero D] {K E Gadget : Type} [Field K] [Field E] {e : PaidIdentity K D m}
    {S : Normalized.SiteSchedule e} {shape : ℕ → Shape} {Word : ℕ → Type} [∀ t, Fintype (Word t)]
    {V : ℕ → ℕ → Type} [∀ t j, Fintype (V t j)] {w : ℕ → ℕ → ℕ}
    {R r pins link k axes gridDepth a regs rw ec width s copies : ℕ}
    (p : UniversalMachine.Program)
    (fit : 2*((UniversalMachine.programPrefix p).length+(TeamContraction.cutWidth (k+1)+a))+
      R*link+Wires.innerWidth r regs rw ec width ≤ k+1)
    {order : Fin (tileCount axes gridDepth) ≃ (Fin axes → Deck (gridDepth+2))}
    (W : WiredWitness (tapeTemplate p fit pins) (Fin.last k) D axes gridDepth order
      (0 : ParseTable.State (Fin (k+1) × Bool) s))
    (position : (Fin axes → Deck (gridDepth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (free : Fin (R+1) → Fin r → Fin a → Bool)
    {deep : S.floor+1+S.drop*T ≤ start} (count : (EnrichedOuter.fan S)^T*copies = R+1)
    {good : ∀ j, EnrichedOuter.State S start (Fin (tileCount axes gridDepth))
      (fun _ => copies*inputBlockWidth r (k+1) axes gridDepth) shape Word j → Prop}
    (M : EnrichedOuter.Machine.{0,u} deep good V w) (bottom : EnrichedOuter.Admissible good 0)
    (installed : bottom.val.pack.layout = (wiredGrid (tapeTemplate p fit pins) axes gridDepth order position).groupedRepeat
      (fun _ : Fin (tileCount axes gridDepth) => inputBlockWidth r (k+1) axes gridDepth) order copies)
    (y : e.Entry → E)
    (hy : ∀ f : MvPolynomial e.Entry ℤ, MvPolynomial.eval₂Hom (Int.castRingHom K) e.entry f = 0 →
      MvPolynomial.eval₂Hom (Int.castRingHom E) y f = 0)
    (pos : e.Entry → Gadget) (hg : 0 < inputBlockWidth r (k+1) axes gridDepth)

set_option synthInstance.maxSize 4000
set_option maxRecDepth 8000
set_option maxHeartbeats 1400000

/-- Enumerate the true original batch numbers in the nested public history. -/
noncomputable local instance guardedHistoryBatchFinite {j : ℕ} : Fintype (Port (EnrichedOuter.fan S) (Fin copies × Unit) j) :=
  Replay.batchFinite (EnrichedOuter.fan S) (Fin copies × Unit) j


open BorderVNP.Cube.Physical NativeAssignments Packing.CellAddresses Packing.BottomReports
open Packing.Inherited Site.Programs ParseBatch ParseBatchVerifier Prewire VPVNP.ParseGrammar

variable (q : (packHistory bottom M.epoch T).Index)
    (code : PairedParameters k s ↪ ℕ) {ns se np : ℕ} (origSite : (W.routedFine position).Site ↪ Fin ns)
    (origEdge : (W.routedFine position).Edge ↪ Fin se) (origPort : Fin r × Fin (publicWidth (tapeTemplate p fit pins)) ↪ Fin np)

local notation3 (prettyPrint := false) "net" => network p fit position free count M bottom installed q
local notation3 (prettyPrint := false) "occurrences" => tags p fit W position free count M bottom installed y hy pos hg q
local notation3 (prettyPrint := false) "leaves" => (EnrichedOuter.fan S)^T
local notation3 (prettyPrint := false) "origins" => Fin leaves × (Fin axes → Deck (gridDepth+2))
local notation3 (prettyPrint := false) "slabs" => fun j : origins => W.seedSlab position code origSite origEdge origPort j.2
local notation3 (prettyPrint := false) "decode" => W.bottomChoicesEquiv position origEdge slabs (fun _ => rfl)
local notation3 (prettyPrint := false) "teams" => (SewnTape.teamNumber (EnrichedOuter.fan S) T copies R count).symm

variable {cells cn cd cb ch cK cs sv ed pt demand : ℕ}
    (tile : (network p fit position free count M bottom installed q).Site → Fin cells)
    (siteID : (network p fit position free count M bottom installed q).Site ↪ Fin sv)
    (edgeID : (network p fit position free count M bottom installed q).Edge ↪ Fin ed)
    (portID : FreeBlock R (tileCount axes gridDepth) ↪ Fin pt)
    (state : Site.Programs (network p fit position free count M bottom installed q))
    (host : (Fin ((EnrichedOuter.fan S)^T) × (Fin axes → Deck (gridDepth+2))) ↪
      (network p fit position free count M bottom installed q).Site)
    (recv : Fin demand → Fin cells) (demandWidth : Fin demand → ℕ)
    {edges : ℕ} (cross : (network p fit position free count M bottom installed q).CrossingEdge tile ≃ Fin edges)
    (hd : 0 < cd) (hb : 0 < ch*cb) {load : ℝ} {cellBound : ℕ}
    (budget : PackedLabelBudget (network p fit position free count M bottom installed q) tile recv demandWidth
      load cellBound (cd^(cn+1)))
    (cubePos : TableEntry cn cb ch cK cs → Gadget)
    (bank : Ports (fun _ : FreeBlock R (tileCount axes gridDepth) => inputBlockWidth r (k+1) axes gridDepth))
    (num : Gadget ↪ ℕ) (owner : Fin sv → ℕ) (report : Fin cells → List (List ℕ))

local notation3 (prettyPrint := false) "orderC" => List.finRange cells
private theorem all_cells (c : ℕ) : (List.finRange c).toFinset = Finset.univ := by ext; simp
local notation3 (prettyPrint := false) "placement" => PacketPlacement.ofNativeMean (K := cK) teams cs net tile recv demandWidth cross orderC
  (List.nodup_finRange _) (all_cells _) hd hb budget
local notation3 (prettyPrint := false) "slots" => meanPackedEmbedding net tile recv demandWidth cross orderC (List.nodup_finRange _)
  (all_cells _) cn cd hd hb budget
local notation3 (prettyPrint := false) "owners" => fun sel : Packet cn cd (blocksFor load (ch*cb) (cd^(cn+1))) → Selector cn cK ch =>
  greedyOwner R cb cs (meanPackedLabel net tile recv demandWidth orderC cn cd hd) recv demandWidth sel
local notation3 (prettyPrint := false) "cellBank" => (c : Fin cells) → Fin (externalBase net tile c (placedSize net state)) → Bool
local notation3 (prettyPrint := false) "guard" => GuardedCores net tile siteID edgeID portID state owners slots bank owner report

/-- Recover the original private assignment of every verifier copy and one
passing path of the exact packet on this history. Both directions use the
same original fine cable numbering and physical shared payload. -/
noncomputable def guardedMeanHistoryEquiv
    (widths : ∀ j : origins, (state (host j)).birth.work = copies*(slabs j).stride)
    (model : ∀ z, TagModels net edgeID portID state (occurrences (decode z)).tags num
      (carryPred host (birthPredicate slabs (fun _ => copies) z)))
    (stored : ∀ v, owner (siteID v) = (tile v).val)
    (locality : ∀ v, (state v).birth.Local)
    (schema : ∀ v, (state v).program.Schema) (relative : ∀ v, (state v).program.RelativeBoxes) :
    {a : Routed (b := cb) (s := cs) owners × cellBank // guard a.1 a.2} ≃
      (Σ z : Fin leaves → Fin copies → W.Hidden position, (placement).Passing (occurrences z) bank cubePos) :=
  nativeMeanCoreEquiv net tile siteID edgeID portID state host slabs (fun _ => copies) widths teams recv
    demandWidth cross orderC (List.nodup_finRange _) (all_cells _) hd hb budget bank num decode occurrences model
    owner report stored locality schema relative cubePos


local notation3 (prettyPrint := false) "pinned" => PinnedRaw (s := cs) net tile state owners slots

/-- On the actual routing domain, remove the duplicate endpoint padding
proof and recover the original assignments. The chosen exterior payload and
the local unverified core vectors pass unchanged to the inverse cell map. -/
noncomputable def guardedPinnedMeanHistoryEquiv
    (widths : ∀ j : origins, (state (host j)).birth.work = copies*(slabs j).stride)
    (model : ∀ z, TagModels net edgeID portID state (occurrences (decode z)).tags num
      (carryPred host (birthPredicate slabs (fun _ => copies) z)))
    (stored : ∀ v, owner (siteID v) = (tile v).val)
    (locality : ∀ v, (state v).birth.Local)
    (schema : ∀ v, (state v).program.Schema) (relative : ∀ v, (state v).program.RelativeBoxes) :
    {a : pinned // guard a.1.val a.2} ≃
      (Σ z : Fin leaves → Fin copies → W.Hidden position, (placement).Passing (occurrences z) bank cubePos) :=
  (pinnedGuardsEquiv net tile siteID edgeID portID state owners slots bank owner report).trans
    (nativeMeanCoreEquiv net tile siteID edgeID portID state host slabs (fun _ => copies) widths teams recv
      demandWidth cross orderC (List.nodup_finRange _) (all_cells _) hd hb budget bank num decode occurrences model
      owner report stored locality schema relative cubePos)

end Diagonal.CellEntries.EnrichedTape

end BorderVNP
end Computability
end OAI
