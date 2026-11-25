import OAI.Hierarchy.DescentOverlapTables

namespace OAI
/-! # Address layout for moving reset operands into the next compact host order -/
namespace Hierarchy.DescentResetRetainedPlacement
open DescentSIMDLookup ProtocolRAM
noncomputable section

structure Chart where
  oldHosts : ℕ
  newHosts : ℕ
  shapes : ℕ
  groups : ℕ
  blocks : ℕ
  lanes : ℕ

structure Batch where
  fields : ℕ
  bits : ℕ
  inputLanes : ℕ

namespace Chart
variable (v : Chart) (b : Batch)
def parts := chunks v.groups v.lanes
def sparse := v.oldHosts*v.shapes
def rows := v.newHosts*v.parts
def rounded (n : ℕ) := 2^Nat.clog 2 (n+1)
/-- Exact end of the original overlap and group/block transpose, including the live page guard. -/
def projected (floor : ℕ) :=
  let oldGroups:=v.groups*v.blocks
  let copied:=floor+rounded (b.fields*(v.oldHosts*chunks oldGroups b.inputLanes))
  let converted:=Overlap.dest copied (b.fields*v.oldHosts) oldGroups b.inputLanes (v.lanes*v.blocks) b.bits
  let transposed:=converted+rounded ((b.fields*v.oldHosts)*chunks oldGroups (v.lanes*v.blocks))
  let dictionary:=v.blocks*2^((b.bits*v.blocks)*v.lanes)
  let entries:=b.fields*(v.blocks*((v.oldHosts*1)*v.parts))
  transposed+(dictionary+2*entries)+rounded dictionary+rounded entries+entries+rounded (v.oldHosts*v.parts)
/-- Static one-based row map. Zero selects the discarded shape. -/
def route (floor : ℕ) : Bank := ⟨v.projected b floor,Nat.clog 2 (v.sparse*v.parts+1)⟩
def directory (floor : ℕ) := (v.route b floor).base+(v.route b floor).size
def samples (floor : ℕ) := v.directory b floor+(2*2^Nat.clog 2 v.rows+2^Nat.clog 2 v.sparse)
def bank (floor : ℕ) (f : Fin b.fields) (x : Fin v.blocks) : Bank :=
  ⟨v.samples b floor+(finProdFinEquiv (f,x)).val*v.rows,Nat.clog 2 (v.rows+1)⟩
def endAddress (floor : ℕ) := v.samples b floor+(b.fields*v.blocks)*v.rows+rounded v.rows
/-- Two typed input arrays can have distinct alphabets and lane counts. The
second scan starts immediately after the retained fields and their donor indices. -/
def placedEndAddress (retained signed : Batch) (floor : ℕ) :=
  v.endAddress signed (v.endAddress retained floor)

theorem projected_affine (floor : ℕ) : v.projected b floor=floor+v.projected b 0 :=by
  simp only [projected,Overlap.dest,Overlap.dictBase,Nat.zero_add,Nat.add_assoc]

theorem affine (floor : ℕ) : v.endAddress b floor=floor+v.endAddress b 0 :=by
  simp only [endAddress,samples,directory,route,Bank.size,v.projected_affine b floor,Nat.add_assoc]

theorem placed_affine (retained signed : Batch) (floor : ℕ) :
    v.placedEndAddress retained signed floor=floor+v.placedEndAddress retained signed 0 :=by
  unfold placedEndAddress
  rw [v.affine signed (v.endAddress retained floor),v.affine retained floor,
    v.affine signed (v.endAddress retained 0),Nat.add_assoc]

end Chart
end
end Hierarchy.DescentResetRetainedPlacement

end OAI
