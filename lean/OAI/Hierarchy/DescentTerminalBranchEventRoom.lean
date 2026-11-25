import OAI.Hierarchy.DescentTerminalPlacedAdmission

namespace OAI
/-! # Terminal event directories stay below the first native scalar write -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open DescentTerminalRowArena
open DescentTerminalVertexFields (MaskedShelf)
open DescentTerminalEmitter (BeforeKey AfterFlights)

noncomputable section

structure BranchEvents (S : Shape) (L : Layout) (w : ℕ) : Prop where
  pages : L.directory.texture.base+(S.sites+1) < 2^w
  stored : L.directory.texture.Fits w L.emit.leaf.event.base
  pagesFit : S.sites+1 ≤ L.directory.texture.size
  preserve : ∀ b ∈ [L.directory.span.active,L.directory.span.owner,L.directory.span.localRow,
    L.directory.ports,L.directory.count,L.directory.firstWord,L.directory.skip,L.directory.countShift,
    L.directory.modeShift,L.directory.skipShift,L.directory.wordShift], b.Fits w L.directory.texture.base
  wordSide : ∀ W ≤ S.terminal.rows, W < 2^w
  eventFit : L.emit.leaf.event.Fits w L.emit.leaf.cells.base
  eventSize : S.terminal.pool ≤ L.emit.leaf.event.size
  frames : ∀ i : Fin S.terminal.pool, let a := L.emit.leaf.event.base+i.val
    BeforeKey S.terminal L.emit a ∧ AfterFlights S.terminal L.emit a ∧ a < L.emit.scalar
  compileLow : (DescentTerminalLeafFold.row L.emit.leaf).Fits w L.emit.leaf.cells.base
  maskAlias : L.emit.leaf.occupancy = L.emit.leaf.cells
  romLow : L.emit.leaf.table.Fits w L.emit.leaf.cells.base

private theorem leafRow_fits (leaf : DescentTerminalLeafFold.Layout) {w : ℕ}
    (lanes : leaf.lanes.Fits w leaf.cells.base) (half : leaf.half.Fits w leaf.cells.base)
    (home : leaf.home.Fits w leaf.cells.base) (eventFit : leaf.event.Fits w leaf.cells.base)
    (weight : leaf.weight.Fits w leaf.cells.base) :
    (DescentTerminalLeafFold.row leaf).Fits w leaf.cells.base := by
  simp only [DescentTerminalLeafFold.row, DescentTerminalHeaderScatter.stage,
    DescentTerminalLeafFold.low, DescentTerminalHeaderScatter.bounded, DescentTerminalLeafFold.address,
    DescentTerminalLeafFold.high, Expr.Fits, true_and, and_true]
  exact ⟨lanes, ⟨home, half⟩, weight, eventFit, half⟩

variable {blocks w : ℕ} (S : Shape) (I : Input) (base : ℕ)
    (F : MaskedShelf blocks) (O : DescentPrivateExponentRAM.Banks)
local notation "A" => rowArena S I base
local notation "L" => layout S I base O
local notation "E" => emitter S I base
local notation "fieldBank" => events A S.terminal.pool
local notation "template" => takeOff S I base
local notation "flights" => DescentTerminalDataPlane.Arena.finish S.terminal.plane template
local notation "slabSize" => DescentTerminalEmitter.Allocation.slab S.terminal I.indexEvents I.formatEvents

set_option maxHeartbeats 1000000 in
/-- The paid event band is placed immediately after the masked home directory.
Only its earlier controls and the other kept input columns are read while the
following cells are filled. -/
theorem branchEvents (old : Earlier S I base F w) (capacity : endAddress S I base < 2^w) :
    BranchEvents S L w := by
  have native := suffix_room S I base F O old capacity
  obtain ⟨pageTop,templateTop,flightTop,emitTop,endTop⟩ := stages S I base
  have alloc : (A).finish < 2^w :=
    pageTop.trans_lt (templateTop.trans_lt (flightTop.trans_lt (emitTop.trans_lt (endTop.trans_lt capacity))))
  have pageLimit : pageEnd S I base < 2^w :=
    templateTop.trans_lt (flightTop.trans_lt (emitTop.trans_lt (endTop.trans_lt capacity)))
  have cellBase : template ≤ (E).leaf.cells.base := flightTop.trans (Nat.le_add_right flights (7*slabSize))
  have stop : template < 2^w := flightTop.trans_lt (emitTop.trans_lt (endTop.trans_lt capacity))
  have below (b : Bank) (end_ : b.base+b.size ≤ template) : b.Fits w (E).leaf.cells.base :=
    ⟨Nat.two_pow_pos _,by have := end_.trans_lt stop; omega,end_.trans cellBase⟩
  have dir (j : Fin 8) : (I.directory j).Fits w (A).finish :=
    ⟨Nat.two_pow_pos _,by have := (old.gather j).trans_lt alloc; omega,old.gather j⟩
  have input (j : Fin 43) :
      (DescentTerminalEmitter.Compact.view (pageEnd S I base) I.sources j).Fits w (E).leaf.cells.base :=
    below _ (DescentTerminalEmitter.Compact.sources_below _ _ old.originals j)
  have table : (E).leaf.table.Fits w (E).leaf.cells.base := input 42
  have half : (E).leaf.half.Fits w (E).leaf.cells.base := input 37
  have home : (E).leaf.home.Fits w (E).leaf.cells.base := input 39
  have weight : (E).leaf.weight.Fits w (E).leaf.cells.base := input 41
  have ev : (E).leaf.event = fieldBank := by
    change inputs S I base 40 = _
    simp [inputs]
  have capEv : S.terminal.pool ≤ (E).leaf.event.size := by
    rw [ev]
    exact (DescentTerminalDataPlane.Arena.room _).le
  have keptEv : (E).leaf.event.Fits w (E).leaf.cells.base := by
    rw [ev]
    exact below _ templateTop
  constructor
  · exact native.endPages
  · change (page A).Fits w (E).leaf.event.base
    rw [ev]
    exact ⟨Nat.two_pow_pos _,by
      change (page A).base+(page A).size+(fieldBank).size < 2^w at pageLimit
      omega,le_rfl⟩
  · exact (DescentTerminalDataPlane.Arena.room _).le
  · intro b hb
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (A).fits_band alloc (i:=10) (j:=22) (by decide) (by decide)
    · exact (A).fits_band alloc (i:=11) (j:=22) (by decide) (by decide)
    · exact (A).fits_band alloc (i:=12) (j:=22) (by decide) (by decide)
    · exact dir 0
    · exact dir 1
    · exact dir 2
    · exact dir 3
    · exact dir 4
    · exact dir 5
    · exact dir 6
    · exact dir 7
  · intro W hw
    have := native.issuer.endNames
    omega
  · exact keptEv
  · exact capEv
  · intro i
    have inside : (E).leaf.event.base+i.val < template := by
      rw [ev]
      exact (Nat.add_lt_add_left (i.isLt.trans_le (DescentTerminalDataPlane.Arena.room _).le) _).trans_le templateTop
    constructor
    · constructor <;> change (E).leaf.event.base+i.val < template+_ <;> omega
    constructor
    · apply after_start S I base O
      change (E).leaf.event.base+i.val < template+_
      omega
    · change (E).leaf.event.base+i.val < flights+9*slabSize
      omega
  · exact leafRow_fits (E).leaf native.issuer.before half home keptEv weight
  · rfl
  · exact table

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
