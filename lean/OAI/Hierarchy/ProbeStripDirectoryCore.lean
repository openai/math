import OAI.Hierarchy.ProbePayloadAccounts
import OAI.Hierarchy.ProbeStripAccounts
import OAI.Hierarchy.ProtocolRAMPurchaseShelfRecords
import OAI.Hierarchy.ProtocolRAMPurchaseInventory
import OAI.Hierarchy.ProtocolRAMOccurrenceHeader

namespace OAI
/-! # Addresses of actual strip commodities on the native inventory tape

The payload row supplies its source ordinal directly. A purchased row reads
the recorded DFS trajectory at the requested position. Only the stage and
signed-direction lane prefixes enter the immutable controller text. -/

noncomputable section
namespace Hierarchy.ProtocolRAM.StripDirectory

open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage PurchaseFrozen
open scoped Fin.CommRing Classical

variable {w z N k H R d : ℕ}

def laneOffset (z : ℕ) (j : Fin N) (a : Fin k × Bool) : ℕ :=
  (1+j.val*(2*k)+((PurchaseMarks.signedDirection k).symm a).val)*2^z

/-- The argument of each lookup is a global commodity ordinal relative to
the existing stock snapshot. -/
def payloadSlot (z : ℕ) : PayloadStrip.Quotes N k → Expr
  | .inl _ => .row
  | .inr (j,a) => .op .add (.lit (laneOffset z j a)) .row

theorem payloadSlot_read (m : Memory w) (p : Fin (2^z)) (u : PayloadStrip.Quotes N k) :
    (payloadSlot z u).eval m (p.val:Word w) =
      (PurchaseInventory.slot (PayloadStrip.rowAddress p u) : Word w) := by
  rcases u with _ | ⟨j,a⟩ <;>
    simp [payloadSlot,PayloadStrip.rowAddress,PurchaseInventory.slot,PurchaseInventory.lane,
      PurchaseInventory.record,laneOffset,Expr.eval,RowOp.opcode,BinaryOp.eval,Nat.cast_add]

/-- A genuine tile label from the candidate-major part of the public DFS
slab. Position is fixed in the strip and candidate ordinal is dynamic. -/
def tile (source : Bank) (R j : ℕ) : Expr :=
  .lookup source (.op .add (.lit (j*R)) .row)

theorem tile_read {n : ℕ} (source : Bank) (rows : Fin R → Fin H → Fin n) (m : Memory w)
    (loaded : ProtocolRAMPurchaseGateColumns.TileRows source rows m)
    (size : H*R ≤ source.size) (room : H*R ≤ 2^w) (i : Fin R) (j : Fin H) :
    (tile source R j.val).eval m (i.val:Word w) = ((rows i j).val : Word w) := by
  have «prefix» := Nat.mul_le_mul_right R j.isLt
  rw [Nat.succ_mul] at «prefix»
  have bound : j.val*R+i.val < H*R := by have := i.isLt; omega
  simpa only [tile,Expr.eval,RowOp.opcode,BinaryOp.eval,←Nat.cast_add,Bank.read,
    Fin.val_cast_of_lt (bound.trans_le room),Nat.mod_eq_of_lt (bound.trans_le size)] using
    loaded i j

/-- One signed altimeter on a chain row combines its tile's *runtime*
source ordinal with the fixed stage and signed direction. -/
def chainSlot (z : ℕ) (stage : Fin N) (source : Bank) (R : ℕ) (u : Fin H × (Fin k × Bool)) : Expr :=
  .op .add (.lit (laneOffset z stage u.2)) (tile source R u.1.val)

theorem chainSlot_read {n : ℕ} (stage : Fin N) (source : Bank)
    (rows : Fin R → Fin H → Fin n) (m : Memory w)
    (loaded : ProtocolRAMPurchaseGateColumns.TileRows source rows m)
    (size : H*R ≤ source.size) (room : H*R ≤ 2^w) (i : Fin R) (u : Fin H × (Fin k × Bool))
    (record : Fin (2^z)) (hit : (rows i u.1).val = record.val) :
    (chainSlot z stage source R u).eval m (i.val:Word w) =
      (PurchaseInventory.slot (.inr ((record,stage),u.2)) : Word w) := by
  simp only [chainSlot,Expr.eval,RowOp.opcode,BinaryOp.eval,tile_read source rows m loaded size room,hit,
    PurchaseInventory.slot,PurchaseInventory.lane,PurchaseInventory.record,laneOffset,Nat.cast_add]

/-- The source bank is the very slab populated by the native CT sampler
for this stratum. Its executable address never mentions a permutation. -/
def keySlot (sh : Shelf) (S : PurchaseSampler) (depth : ℕ) (i : Key z d k)
    (u : ChainStrip.Axes depth k) : Expr :=
  chainSlot z (stage i) (sh.L S depth i).source (paths z S.degree depth) u

theorem keySlot_tiles (sh : Shelf) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z)))
    (depth : ℕ) (key : Key z d k) (m : Shelf.Mem z d) (tiles : ProtocolRAMPurchaseGateColumns.TileRows
      (sh.L S depth key).source (Shelf.pathRows S π depth key) m)
    (room : (depth+1)*paths z S.degree depth ≤ 2^(Native.wordBits z d Native.copies))
    (i : PurchaseDirectory.Index (2^z) S.degree depth) (u : ChainStrip.Axes depth k)
    (p : Fin (2^z)) (hit : (Shelf.pathRows S π depth key i u.1).val = p.val) :
    (keySlot sh S depth key u).eval m (i.val:Word (Native.wordBits z d Native.copies)) =
      (PurchaseInventory.slot (.inr ((p,stage key),u.2)) : Word (Native.wordBits z d Native.copies)) := by
  unfold keySlot
  rw [show paths z S.degree depth = (PurchaseDFS.layout (2^z) S.degree depth).length by simp [PurchaseFrozen.paths]]
  apply chainSlot_read _ _ _ _ tiles _ _ _ _ _ hit
  · exact (ProtocolRAMPurchaseSampler.lt_span _).le
  · simpa [PurchaseFrozen.paths] using room

def flagBank (sh : Shelf) (S : PurchaseSampler) (z d k depth : ℕ) : Bank :=
  ⟨sh.flagsBase S z d k depth,ProtocolRAMPurchaseSampler.bits (count z d k*paths z S.degree depth)⟩

/-- Public geometry of the padded key/candidate row directory. -/
def stratumHeader (z d k D depth start : ℕ) : Calendar.StockCommit.PortHeader :=
  ⟨start,count z d k,paths z D depth⟩

/-- The two physical header words identify the key and the candidate in
that key. The same expression is shared across all purchased candidates. -/
def allChainSlot (sh : Shelf) (S : PurchaseSampler) (depth : ℕ)
    (header : Calendar.StockCommit.PortHeader) (u : ChainStrip.Axes depth k) : Expr :=
  chooseField (count z d k) 0 (fun i : Key z d k => (keySlot sh S depth i u).atRow header.fieldTerm) header.ballTerm

theorem allChainSlot_read (sh : Shelf) (S : PurchaseSampler) (depth : ℕ)
    (header : Calendar.StockCommit.PortHeader) (u : ChainStrip.Axes depth k)
    (m : Memory w) (r : Word w) (i : Key z d k) (candidate : Word w)
    (keyFit : count z d k ≤ 2^w) (keyHit : (header.ballTerm.eval m r).val=i.val)
    (rowHit : header.fieldTerm.eval m r=candidate) :
    (allChainSlot (z:=z) (d:=d) sh S depth header u).eval m r =
      (keySlot sh S depth i u).eval m candidate := by
  calc
    _ = ((keySlot sh S depth i u).atRow header.fieldTerm).eval m r :=
      eval_chooseField (count z d k) 0
        (fun j : Fin (count z d k) => (keySlot sh S depth j u).atRow header.fieldTerm)
        header.ballTerm m r i (by simpa using keyFit) (by simpa using keyHit)
    _ = _ := by rw [eval_atRow,rowHit]

/-- One public occurrence ordinal is decoded by its actual mounted quotient
and remainder banks to the original ball and port. -/
theorem header_pair (h : Calendar.StockCommit.PortHeader) (m : Memory w) (loaded : h.Loaded m)
    (i : Fin h.rows) (j : Fin h.ports) :
    let r := ((h.enum ⟨i,j⟩).val : Word w)
    h.ballTerm.eval m r = (i.val:Word w) ∧ h.fieldTerm.eval m r = (j.val:Word w) := by
  have positive := (Nat.zero_le j.val).trans_lt j.isLt
  have div : (j.val+h.ports*i.val)/h.ports=i.val := by
    rw [Nat.mul_comm h.ports i.val,Nat.add_mul_div_right _ _ positive,Nat.div_eq_of_lt j.isLt,Nat.zero_add]
  have mod : (j.val+h.ports*i.val)%h.ports=j.val := by
    rw [Nat.mul_comm h.ports i.val,Nat.add_comm j.val]
    exact Nat.mul_add_mod_of_lt j.isLt
  have position : (h.enum ⟨i,j⟩).val = j.val+h.ports*i.val := rfl
  exact ⟨(loaded.first (h.enum ⟨i,j⟩)).trans (by rw [position,div]),
    (loaded.second (h.enum ⟨i,j⟩)).trans (by rw [position,mod])⟩


end Hierarchy.ProtocolRAM.StripDirectory
end

end OAI
