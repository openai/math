import OAI.Computability.BorderVNP.DiagonalReceivedSparseCall
import OAI.Computability.BorderVNP.DiagonalSignedMeasuredField
import OAI.Computability.BorderVNP.CellSparseExteriorTeamCost

/-! # Exact signed call budgets on the true stable fragment rows -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeAssignments
set_option maxRecDepth 9000
set_option maxHeartbeats 1200000

open Crossing Packing Packing.CellAddresses Packing.BottomReports Packing.Inherited
open Site.Programs CellSparse DiagonalTallyCellReports RoutingISA CompactMachine TeamScales

variable {a : SignedTaskArena.Layout} {T D ns ne np : ℕ} {P J Origin : Type} [Fintype P] [Fintype J] {bits : P → ℕ} {layout : Fin T → ReportLayout}
    (R : ReceivedRows layout a.cube.cells) (N : Network D P bits) (cell : N.Site → Fin a.cube.cells)
    (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin ne) (portID : P ↪ Fin np)
    (owner : Fin ns → ℕ) (state : Site.Programs N)
    (host : J ↪ N.Site) (bundle : J → Bundle) (origins : Fin a.cube.cells → List J)
    {M E Z high table H coeff k B j n r w : ℕ}
    (b : ReceivedBounds R N cell siteID owner state host bundle origins M E Z high table H
      (coeff*(logWidth r n+1)^k))
    (paid : SparseExterior.PrivateCallsAt 3076 table (B+10) (j+1) H coeff k n r)
    (u : Fin T)
open VPVNP.BurstRAM TypedTaskBuilder FragmentRows Diagonal.ExternalSew.Fragments

variable {f : FragmentRows.Layout} {mem : Memory w} {fit : f.Fits w (readings mem)} {cells : a.fragments.cells=f.cells}
    (e : SparseEmission a f mem fit cells) {team frame offsets ctl live ports : ℕ} {data : ℕ → ℕ → Bool}
local notation3 (prettyPrint := false) "arena" => a.controlRows team frame offsets ctl live ports
local notation3 (prettyPrint := false) "raw" => readings e.output
local notation3 (prettyPrint := false) "num" => (arena).before raw (arena).cells
local notation3 (prettyPrint := false) "idx" => globalCell (arena).toLayout raw
variable (rows : (i : Fin ((a.controlRows team frame offsets ctl live ports).toLayout.before (readings e.output) a.cube.cells)) →
  SparseCell a f mem data i.val)
local notation3 (prettyPrint := false) "source" => SparseEmission.globalCells (team:=team) (frame:=frame) (offsets:=offsets)
  (ctl:=ctl) (live:=live) (ports:=ports) e rows
local notation3 (prettyPrint := false) "wire" => fun v => (cell v).val
local notation3 (prettyPrint := false) "programs" => fun v => (state v).program
local notation3 (prettyPrint := false) "base(" c ")" => FinalCell.countBase N wire programs (c).val
local notation3 (prettyPrint := false) "inputs(" c ")" => FinalCell.cellInput N wire siteID edgeID portID owner programs
  (c).val (layout u).gadgets (layout u).countWidth

include b paid in
/-- Apply the selected private-call schedule to the physical source width,
actual stable nonempty spans, and this proposal's report bytes. The unique
owned-array ordinal gives every globally addressed call its exact cutoff. -/
theorem ReceivedBounds.scheduled_emitted_calls
    (hn : 1≤n) (hr : 1≤r) (hH : 9≤H) (hm : M≤TeamScales.width n (1/5)) (he : E≤TeamScales.width n (1/4))
    (hw : 0<w) (hwn : w≤n) (digits : high.size+1≤B*(logWidth r n+1)^j) (size : 3*M+Z≤4*(M+E+1)^3)
    (count : num=(R.cells u).length) (order : ∀ i, (rows i).number.val=idx i.val)
    (cellsAt : ∀ i : Fin num, (rows i).number=R.order ⟨u,Fin.cast count i⟩)
    (widths : ∀ i : Fin num, readings mem (f.supplied+(rows i).number.val)=suppliedSize N wire (rows i).number.val)
    (tails : ∀ i : Fin num, (rows i).tail.length=((R.cells u).get (Fin.cast count i)).tailWidth)
    (p : ℕ → CellPacket.Placed Origin) (extra : ℕ → List Record)
    (seen : ∀ i : Fin (R.cells u).length, let c := R.order ⟨u,i⟩; let field := (source c.val).field
      SparseExterior.logicalCell (p c.val) (extra c.val) field =
        FinalCell.withWiring (inputs(c) field.values)
          (supplements (base(c)+(layout u).gadgets*(layout u).countWidth) ((origins c).map bundle))) :
    ∀ c < (arena).cells, (arena).owner raw c=(arena).team →
      let field := (source c).field
      let logical := SparseExterior.logicalCell (p c) (extra c) field
      (CompactFrame.pack w (Packet.input logical.directory logical.privateWires field.bytes)).length≤TeamScales.width n (1/2) ∧
        logical.directory.ProfileWidths ∧ SparseExterior.clock w logical.directory logical.privateWires field≤n^25 := by
  intro c hc owned field logical
  let target : Fin a.cube.cells := ⟨c,hc⟩
  obtain ⟨i,number,width,trail,sorted,positive⟩ := e.measuredField rows order target owned
  let j₀ := Fin.cast count i
  have received : R.order ⟨u,j₀⟩=target := (cellsAt i).symm.trans number
  have receivedIndex : (R.order ⟨u,j₀⟩).val=c := congrArg Fin.val received
  have extent : field.width=suppliedSize N wire (R.order ⟨u,j₀⟩).val := by
    rw [received]
    exact width.trans (number ▸ widths i)
  have tail : field.tail.length=((R.cells u).get j₀).tailWidth :=
    (congrArg List.length trail).trans (tails i)
  have actual := seen j₀
  have typed : SparseExterior.logicalCell (p c) (extra c) field =
      FinalCell.withWiring (inputs(R.order ⟨u,j₀⟩) field.values)
        (supplements (base(R.order ⟨u,j₀⟩)+(layout u).gadgets*(layout u).countWidth) ((origins (R.order ⟨u,j₀⟩)).map bundle)) := by
    simpa only [receivedIndex] using actual
  exact b.scheduledArgument R N cell siteID edgeID portID owner state host bundle origins paid u j₀
    hn hr hH hm he hw hwn digits size field sorted positive extent tail (p c) (extra c) typed

end Cube.Physical.NativeAssignments

end BorderVNP
end Computability
end OAI
