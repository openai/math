import OAI.Computability.BorderVNP.DiagonalSparseReportDelivery
import OAI.Computability.BorderVNP.DiagonalSignedPreparedPlacements
import OAI.Computability.BorderVNP.FiniteEvaluatorProducedCellMemory

/-! # The actual history geometry fields of the issued signed argument -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.History.Native

open VPVNP.BurstRAM RoutingISA CellPacket SignedTaskArena CellSparse Packet Source
open Packing.Inherited FrozenTape SiteWords LiveWords DiagonalTallyCellReports

variable {aSlots cap d t wp wd hdr ctrl : ℕ} {R B U V E Z : Type}
    {a : SignedTaskArena.Layout} (dir : Packing.Directory.Layout)
    (S : FrozenTape.Schema R B) (L : FrozenTape.Schema U V) (entry : Fin dir.entries ↪ Fin aSlots)
    (known : Fin aSlots → List (List Factor)) (sh : ∀ i, (S.tags i).length≤cap) (lh : ∀ i, (L.tags i).length≤cap)
    (priv : Fin (a.cube.cells+1) → E) (rep : Fin (a.cube.cells+1) → List (List E)) (arg : E → ℕ)
    (x : Pins R B d → Bool) (y : Pins U V t → Bool) (cells : Fin aSlots → Fin a.cube.cells)
    (off box : Fin aSlots → ℕ) (ptr : Fin dir.entries → Z) (base : ℕ → ℕ) (slot : Fin dir.entries → ℕ)
    (body : Fin dir.entries → List Factor) (rows : CellControlRows.Layout) (raw : ℕ → ℕ)
set_option quotPrecheck false
local notation3 (prettyPrint := false) "G" => directory S L (originalBoxes entry known) sh lh priv rep arg x y cells off box
local notation3 (prettyPrint := false) "template₀" => template S L (originalBoxes entry known) sh lh priv rep
local notation3 (prettyPrint := false) "site" => cellOf S L x y cells
local notation3 (prettyPrint := false) "fields" => fun i => scalarArgs (cap:=cap) S L x y off box ((roster aSlots S L).get i)
local notation3 (prettyPrint := false) "pubRoom" => (a.cube.cells+1)+(G).words.length+(a.cube.cells+1)≤2^wp
local notation3 (prettyPrint := false) "descRoom" => (a.cube.cells+1)+(Schema.coords ((G).referenceRows ptr).length).length+(a.cube.cells+1)≤2^wd

set_option maxHeartbeats 950000 in
/-- The frozen history's physically placed outputs supply all public template
and hidden ordinal fields of the pre-call. The spare cell participates in the
sort, while the finite gadget count and each private box pointer are read on
the genuine submitted real cell. -/
theorem issuedSourceGeometry (hf : pubRoom) (hs : descRoom) (physical : ℕ → Placed (Fin dir.entries))
    (moved : physical=Terminal.placeAt (signedPlaces (a:=a) (ctl:=ctrl) (H:=hdr) G ptr base slot body rows raw hf hs))
    (pp : ℕ → ℕ × ℕ) (sent : ∀ j, (pp j.val).1=(cells (entry j)).val)
    (chart : ReportLayout) (count : ∀ c : Fin a.cube.cells, ∃ b, (G).reports c.castSucc=countFields b chart.gadgets chart.countWidth)
    (fits : ∀ j, hdr+(boxBody (body j)).length≤dir.description) :
    Nonempty (dir.OriginalBoxRows pp (fun c : Fin a.cube.cells => physical c.val)) ∧
    TypedBatch.SourceFootprint (fun c : Fin (a.cube.cells+1) => physical c.val) ((template₀).directory site arg fields) ∧
    (a.cube.cells+1)+(template₀).atoms.length+(a.cube.cells+1)≤2^wp ∧
    (a.cube.cells+1)+(Schema.coords (template₀).chunkLabels.length).length+(a.cube.cells+1)≤2^wd ∧
    (∀ c : Fin a.cube.cells, (physical c.val).reports.length=chart.gadgets) ∧
    (∀ c : Fin a.cube.cells, ∀ v ∈ (physical c.val).reports, v.length=chart.countWidth) ∧
    (∀ c : ℕ, ∀ j, (physical c).headerWidth+(boxBody ((physical c).factors j)).length≤dir.description) := by
  let pl := signedPlaces (a:=a) (ctl:=ctrl) (H:=hdr) G ptr base slot body rows raw hf hs
  have atSlot (c : Fin (a.cube.cells+1)) : physical c.val=pl c := by
    rw [moved]
    exact congrArg pl (Fin.ext (Nat.min_eq_left (Nat.le_of_lt_succ c.isLt)))
  have shape : TypedBatch.SourceShape (fun c : Fin (a.cube.cells+1) => physical c.val) G := by
    rw [show (fun c : Fin (a.cube.cells+1) => physical c.val)=pl from funext atSlot]
    exact ⟨fun _ => rfl,fun _ => rfl,fun _ => rfl,fun _ => rfl⟩
  let ungrouped := (template₀).directory site arg fields
  have same : (G).words.length=ungrouped.words.length :=
    ungrouped.regroup_wordCapacity (anchor S L x y) rfl (anchored S L x y cells)
  have volume : TypedBatch.SourceFootprint (fun c : Fin (a.cube.cells+1) => physical c.val) ungrouped :=
    ⟨shape.footprint.publicWords.trans same,fun c => congrArg List.length (shape.boxes c)⟩
  have pub : (G).words.length=(template₀).atoms.length := same.trans ((template₀).wordCapacity site arg fields)
  have chunks := directory_chunk_count S L (originalBoxes entry known) sh lh priv rep arg x y cells off box ptr
  have reports (c : Fin a.cube.cells) : (physical c.val).reports=(G).reports c.castSucc := shape.reports c.castSucc
  refine ⟨⟨originalPlacedRows dir pp S L entry known sh lh priv rep arg x y cells off box _
    (fun c => shape.boxes c.castSucc) sent⟩,volume,?_,?_,?_,?_,?_⟩
  · rwa [←pub]
  · rwa [chunks]
  · intro c
    obtain ⟨b,hb⟩ := count c
    rw [reports c,hb,countFields_length]
  · intro c v hv
    obtain ⟨b,hb⟩ := count c
    rw [reports c,hb] at hv
    change v ∈ List.ofFn _ at hv
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hv
    exact List.length_ofFn
  · intro c j
    rw [moved]
    exact fits j

end CellPacketGeometry.History.Native

end BorderVNP
end Computability
end OAI
