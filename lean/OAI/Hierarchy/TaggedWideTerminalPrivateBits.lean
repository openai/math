import OAI.Hierarchy.TaggedWidePrivateBits
import OAI.Hierarchy.TaggedWideWindowMask
import OAI.Hierarchy.ProtocolRAMEmit

namespace OAI
/-! # The final reporter's physical width at each retained private data pair -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open ThreeFlat Routing
open Computability.VPVNP.BurstRAM PrivateRAM Diagonal TraceWords
open ProbeStage ProbeStage.CoreBoard Tagged WidePadding WideStack WideStack.Leaf WideControlJoin
open scoped Classical Fin.CommRing BigOperators
def Board.privateWidthRow (board : Board) (G : Gate) (dst : ℕ)
    (room : dst+9*board.rows ≤ G.u) (i : Fin board.rows) : Fin G.u :=
  ⟨dst+3*board.rows+3*i.val+1, by have bound := i.isLt; omega⟩

variable {F : Type} [Field F] {S : PurchaseSampler} {h W k width : ℕ}
  (board : Board) (order : Fin board.coreRows ≃ Edges S h (2^W) k)
  {E Se D : Type} [Fintype E] [Fintype Se] [Fintype D] (G : Gate) (dst : ℕ)
  (room : dst+9*board.rows≤G.u) (narrow : WideParent.columnBits width≤G.W+1)
local notation "b" => WideParent.columnBits width
local notation "V" => SitePins E Se D G

def Board.privateWidthPin (i : Fin board.rows) (j : Fin b) : V :=
  .inr (.inr (.inr (board.privateWidthRow G dst room i,j.castLE narrow)))

def Board.privatePaired (data : Bool→board.Private order→Fin width→V) :=
  board.privateBits (F:=F) order (WideParent.column_lt width).le
    (board.privateWidthPin (E:=E) (Se:=Se) (D:=D) G dst room narrow) data

/-- All active private bits use the corresponding physical metric triple. The
proof also covers a dormant private edge with both entire shared words zero. -/
theorem Board.privatePaired_read (data : Bool→board.Private order→Fin width→V)
    (raw : Fin board.rows→ProtocolRAMEmit.Row) (initial final : Memory G.W) (volts : V→Bool)
    (addresses : ∀i,(G.addr (board.privateWidthRow G dst room i)).val=dst+3*board.rows+3*i.val+1)
    (frame : ∀a,dst≤a→a<dst+9*board.rows→final a=ProtocolRAMEmit.emitted dst raw initial a)
    (reads : ∀i j,volts (board.privateWidthPin (E:=E) (Se:=Se) (D:=D) G dst room narrow i j)=
      G.terminal final (board.privateWidthRow G dst room i,j.castLE narrow))
    (maxWidth : ∀i:board.Private order,(raw i.val).width≤width)
    (fits : ∀i:board.Private order,(raw i.val).width<2^G.W) :
    TypedWiring.value (board.privatePaired (F:=F) order G dst room narrow data) volts =
      if EndsPadded (fun i=>(raw i.val).width) (fun _ : board.Private order=>width)
        (fun side i j=>volts (data side i j))
      then ∏i : board.Private order,if ∀j : Fin width,j.val<(raw i.val).width→
        volts (data false i j)=volts (data true i j) then 1 else 0 else 0 := by
  let addr (i:Fin board.rows):=board.privateWidthRow G dst room i
  let words (i:Fin board.rows):=WideParent.column width (final (G.addr (addr i)).val)
  have low (i : Fin board.rows) (j : Fin b) :
      volts (board.privateWidthPin (E:=E) (Se:=Se) (D:=D) G dst room narrow i j)=bits (words i) j := by
    rw [reads]
    change (final (G.addr (addr i)).val).val.testBit j.val=((final (G.addr (addr i)).val).val%2^b).testBit j.val
    simp [Nat.testBit_mod_two_pow,j.isLt]
  have actual (i:board.Private order) : (words i.val).val=(raw i.val).width := by
    let a:=dst+3*board.rows+3*i.val.val+1
    have locate : (G.addr (addr i.val)).val=a:=addresses i.val
    have emitter : ProtocolRAMEmit.emitted dst raw initial a=((raw i.val).width : Word G.W) :=
      (ProtocolRAMEmit.emitted_read dst raw initial i.val 1).2.1
    have read : (final a).val=(raw i.val).width := by
      rw [frame a (by dsimp [a];omega) (by dsimp [a];have:=i.val.isLt;omega),emitter]
      exact Nat.mod_eq_of_lt (fits i)
    change (WideParent.column width (final (G.addr (addr i.val)).val)).val=_
    rw [locate,WideParent.column_read _ _ (read.le.trans (maxWidth i)),read]
  rw [Board.privatePaired,board.privateBits_value order (WideParent.column_lt width).le _ data volts words low]
  simp_rw [actual]


end Hierarchy.ProtocolRAM.Calendar.CatalogueRows

end
end OAI
