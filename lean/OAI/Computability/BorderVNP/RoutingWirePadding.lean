import OAI.Computability.BorderVNP.RoutingWireReads
import OAI.Computability.BorderVNP.TransmissionAcross
import OAI.Computability.BorderVNP.RoutingISAPaddingSchedule

/-! # Padding scans of the physical routing blocks

The scan begins immediately after both directed legs. Its endpoint is the actual
processor count times the link width. In either orientation these are exactly
the padding components of the corresponding unordered block.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout Routing RoutingISA

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
  {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}

/-- Scanning one partner's physical suffix is equivalent to requiring all padding
variables in the associated unordered message block to be zero. -/
theorem TransferBank.padding_iff (hw : 0 < w) {u : Fin (R+1)}
    (A : TransferBank G pin ext L.width w L.header u) (v : Fin (R+1)) (hd : u ≠ v) :
    let f := G.transferFrame u L.header A.dst
    f.ZeroFrom (readings A.mem) (f.usedPrefix A.schedule.fit L.width v) v ↔
      ∀ i : Fin (L.slack (blockOf u v hd)), (L.exteriorEquiv ext).padding ⟨blockOf u v hd,i⟩ = false := by
  intro f
  let b := blockOf u v hd
  let start := L.header + (legLoad L.three L.width b.val.1 b.val.2 + legLoad L.three L.width b.val.2 b.val.1)
  have hs : f.usedPrefix A.schedule.fit L.width v = start := by
    change L.header + legLoad L.three L.width u v + legLoad L.three L.width v u = _
    by_cases huv : u < v <;> simp [start,b,blockOf,huv,Nat.add_assoc,Nat.add_comm]
  have cap : f.capacity = r*link := Nat.mul_comm ..
  have room : start ≤ r*link := by simpa only [start,Nat.add_assoc] using L.fits b
  have len : L.slack b = r*link-start := by simp only [WireLayout.slack,start,Nat.add_assoc]
  have read (i : Fin (L.slack b)) : readings A.mem (f.addr v (start+i.val)) =
      ((L.exteriorEquiv ext).padding ⟨b,i⟩).toNat := by
    simpa only [start,b,f,BroadcastFrame.addr,Wiring.transferFrame,Nat.add_assoc] using
      G.read_message_padding L u v hd pin ext A.ibase A.hbase A.starbase A.mem A.physical hw i
  rw [hs]
  constructor
  · intro h i
    apply Bool.toNat_eq_zero.mp
    rw [← read i]
    apply h _ (Nat.le_add_right ..)
    have hi : i.val < r*link-start := len ▸ i.isLt
    omega
  · intro h j hstart hj
    let i : Fin (L.slack b) := ⟨j-start,by rw [len]; omega⟩
    have he : start+i.val = j := Nat.add_sub_of_le hstart
    exact he ▸ (read i).trans (Bool.toNat_eq_zero.mpr (h i))

/-- All teams' actual suffix scans check exactly all global padding bits. -/
theorem transfer_padding_iff (hw : 0 < w)
    (A : ∀ u, TransferBank G pin ext L.width w L.header u) :
    (∀ u v : Fin (R+1), u ≠ v →
      let f := G.transferFrame u L.header (A u).dst
      f.ZeroFrom (readings (A u).mem) (f.usedPrefix (A u).schedule.fit L.width v) v) ↔
      ∀ i, (L.exteriorEquiv ext).padding i = false := by
  constructor
  · intro h i
    obtain ⟨⟨⟨u,v⟩,huv⟩,i⟩ := i
    have hp := ((A u).padding_iff hw v huv.ne).mp (h u v huv.ne)
    have hb : blockOf u v huv.ne = ⟨(u,v),huv⟩ := by simp [blockOf,huv]
    rw [hb] at hp
    exact hp i
  · intro h u v hd
    exact ((A u).padding_iff hw v hd).mpr fun _ => h _

end TeamContraction

end BorderVNP
end Computability
end OAI
