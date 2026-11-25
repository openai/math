import OAI.Hierarchy.DescentPackedChildPeerQuery
import OAI.Hierarchy.DescentParentFilterFused

namespace OAI
/-! # The shared unary peer-key instruction for a measured parent operand -/
namespace Hierarchy.DescentOrdinarySocketPeer
open DescentSharedCableNames DescentParallelBase DescentParallelBase.ParentFilter DescentSIMDLookup
open DescentHaloWalkRAM DescentPackedZip DescentPackedChildNeighbor
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
def key (D Q K cap b : ℕ) (row : Cell (b*11)) : Cell (Packed.bits ((breadth D*breadth D)*Q)) :=
  PeerQuery.chip ((breadth D*breadth D)*Q) K cap (Machine.scalar D Q K cap b row)
def bits (b M : ℕ) := b*11*M
def table (D Q K cap b M i : ℕ) : ℕ :=
  if hi:i<2^bits b M then (DescentSIMDLookup.table (M:=M) (key D Q K cap b) ⟨i,hi⟩).val else 0
def query (base b M : ℕ) (raw : Expr) : Expr := .lookup ⟨base,bits b M⟩ raw

theorem at_raw {H D Q K cap b : ℕ} {R : Fin H→Fin D→Option (Fin H)} (r : Option (Fused.Raw R Q K cap b)) :
    key D Q K cap b (encode b 11 (Fused.columns r))=PeerQuery.number (Fused.filtered r) := by
  rw [key,Fused.field_read,PeerQuery.chip_at]

theorem at_zero (D Q K cap b : ℕ) : key D Q K cap b 0=0 := by
  simp [key,Machine.absent,PeerQuery.chip_zero]

theorem read {D Q K cap b M H N g w : ℕ} {R : Fin N→Fin D→Option (Fin N)}
    (base limit : ℕ) (src : Expr) (m : Memory w)
    (bankFit : (Bank.mk base (bits b M)).Fits w limit)
    (tableWords : ∀i:Fin (2^bits b M),m (base+i.val)=(table D Q K cap b M i.val:Word w))
    (raw : Fin H→Fin g→Option (Fused.Raw R Q K cap b))
    (old : Source src (fun h j=>encode b 11 (Fused.columns (raw h j))) M m) :
    Source (query base b M src) (fun h j=>PeerQuery.number (Fused.filtered (raw h j))) M m := by
  intro pos
  let n:=data (fun h j=>encode b 11 (Fused.columns (raw h j))) pos
  change (Bank.mk base (bits b M)).read m _=_
  rw [old pos,bank_read _ _ n.isLt bankFit,tableWords n]
  unfold table
  rw [dite_eq_left (show n.val < 2 ^ bits b M from n.isLt)]
  apply congrArg (fun z : Cell ((Packed.bits ((breadth D*breadth D)*Q))*M)=>(z.val:Word w))
  change DescentSIMDLookup.table (key D Q K cap b) n=_
  simp only [DescentSIMDLookup.table,n,data,Equiv.symm_apply_apply]
  apply congrArg (encode _ _)
  funext s
  by_cases inRange : pos.2.val*M+s.val<g <;> simp [inRange,at_raw,at_zero]

end
end Hierarchy.DescentOrdinarySocketPeer

end OAI
