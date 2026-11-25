import OAI.Computability.BorderVNP.CellSparseExteriorBudget

/-! # Length-only scratch and burst reservations for genuine signed cell calls -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open TeamScales VPVNP.BurstRAM CellMacro CellSparse
open private small_width from OAI.Computability.BorderVNP.RoutingISATypedPrivateClock
open private frame_length from OAI.Computability.BorderVNP.RoutingISACompactFrame

/-- Each unpacked private argument has its own address window. The bound is
independent of its actual source directories and guessed report bits. -/
def scratchWindow (n : ℕ) := (n+1)^2

/-- A packed private call uses no more than the physical square-root probe
bound, hence fits this integral length-only window. -/
def burstWindow (n : ℕ) := n+1

/-- The true framed burst occupies enough physical bits to recover its payload. -/
theorem packed_payload_room {w : ℕ} (hw : 0<w) (payload : List Bool) :
    payload.length ≤ w*(CompactFrame.pack w payload).length := by
  have h := TeamPrivateCall.inputBits_length (CompactFrame.pack w payload)
  rw [CompactFrame.inputBits_pack hw,List.length_append,List.length_replicate,frame_length] at h
  rw [Nat.mul_comm]; omega

/-- The actual private burst's certified probe bound covers all three
reservations: raw compact exterior bytes, unpacked scratch and packed words. -/
theorem windows_of_packet {w n p : ℕ} (D : Directory) (f : SparseExterior.Field)
    (hn : 1≤n) (hw : 0<w) (width : w≤n)
    (packed : (CompactFrame.pack w (Packet.input D p f.bytes)).length ≤ TeamScales.width n (1/2)) :
    f.bytes.length ≤ scratchWindow n ∧ (Packet.input D p f.bytes).length ≤ scratchWindow n ∧
      (CompactFrame.pack w (Packet.input D p f.bytes)).length ≤ burstWindow n := by
  have count := packed.trans (small_width hn (1/2) (by norm_num))
  have digits := (packed_payload_room hw (Packet.input D p f.bytes)).trans (Nat.mul_le_mul width count)
  have sq : n*n ≤ scratchWindow n := by unfold scratchWindow; nlinarith
  have src : f.bytes.length ≤ (Packet.input D p f.bytes).length := by simp [Packet.input]
  exact ⟨src.trans (digits.trans sq),digits.trans sq,count.trans (Nat.le_succ _)⟩

/-- Apply the selected schedule's authentic private interpreter receipt to
a sorted sparse cell. No separate bound on its encoded payload is required. -/
theorem windows_from_private {A T B j H R k n r : ℕ} (receipt : SparseExterior.PrivateCallsAt A T B j H R k n r)
    (hn : 1≤n) (M E w p U : ℕ) (hM : M≤width n (1/5)) (hE : E≤width n (1/4)) (hw : 0<w) (hW : w≤n)
    (D : Directory) (f : SparseExterior.Field) (size : f.width+f.tail.length≤E)
    (order : SparseExterior.Ordered f.width 0 f.spans) (positive : ∀ z ∈ f.spans, 0<z.bits.length)
    (static : D.StaticBounds A M) (compact : D.CompactFields p (4*(M+E+1)^3))
    (records : D.records.length≤4*(M+E+1)^3) (reports : D.reportedCounts.length≤4*(M+E+1)^3)
    (mass : Packet.storedMass D≤A*(M+1)^2) (raw : Packet.RawFields D p U) (digits : U.size+1≤B*(logWidth r n+1)^j)
    (shapes : ∀ row ∈ D.records, (Packet.record row).length≤H)
    (tables : ∀ fs ∈ D.boxes, ∀ z ∈ fs, z.TableBound T)
    (counts : ∀ bs ∈ D.reportedCounts, bs.length≤R*(logWidth r n+1)^k) :
    f.bytes.length ≤ scratchWindow n ∧ (Packet.input D p f.bytes).length ≤ scratchWindow n ∧
      (CompactFrame.pack w (Packet.input D p f.bytes)).length ≤ burstWindow n :=
  windows_of_packet D f hn hw hW (receipt M E w p U hM hE hw hW D f size order positive static compact
    records reports mass raw digits shapes tables counts).1

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
