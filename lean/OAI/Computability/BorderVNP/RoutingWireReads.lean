import OAI.Computability.BorderVNP.RoutingWireMessages
import OAI.Computability.BorderVNP.TransmissionExteriorWire

/-! # Native reads of the header, two transmission legs and padding

The routing program reads words of initialized RAM at physical processor addresses.
The wire-layout equivalence identifies each such word with its Boolean component
in the common exterior assignment, including at the higher endpoint of a block.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout Routing RoutingISA

variable {R r t d link inner n w : ℕ} {Edge : Type} (G : Wiring R r t d link inner n Edge)
  (L : WireLayout (R+1) r link) (u v : Fin (R+1)) (hne : u ≠ v) (pin : Fin d → Bool)
  (ext : Exterior R r link → Bool) (ibase hbase starbase : ℕ) (m : Memory w)
  (physical : (G.processorFields u pin ext ibase hbase starbase).ContainsInput m)

private theorem exterior_region (b : Block (R+1)) (z : L.Slot b) :
    ext (b,L.coordinates b z) = L.regionValues (L.exteriorEquiv ext) b z := by
  have h := congrFun (L.exteriorEquiv.symm_apply_apply ext) (b,L.coordinates b z)
  change L.regionValues _ b ((L.coordinates b).symm (L.coordinates b z)) = _ at h
  simpa only [Equiv.symm_apply_apply] using h.symm

include physical

/-- Physical RAM read for any of the four regions of the actual unordered block. -/
theorem Wiring.read_message_region (hw : 0 < w) (z : L.Slot (blockOf u v hne)) :
    readings m (physicalBitAddress u.val (R+1) (G.program.length+t) link v.val
      (L.position (blockOf u v hne) z).val) =
      (L.regionValues (L.exteriorEquiv ext) (blockOf u v hne) z).toNat := by
  exact (G.read_exterior_val hw u v hne pin ext ibase hbase starbase m physical _).trans
    (congrArg Bool.toNat (exterior_region L ext (blockOf u v hne) z))

/-- The actual processor RAM prefix returns the broadcast component of its shared block. -/
theorem Wiring.read_message_header (hw : 0 < w) (i : Fin L.header) :
    readings m (physicalBitAddress u.val (R+1) (G.program.length+t) link v.val i.val) =
      ((L.exteriorEquiv ext).broadcast (blockOf u v hne) i).toNat :=
  G.read_message_region L u v hne pin ext ibase hbase starbase m physical hw (.inl i)

/-- The actual padding scan reads each bit of the unused suffix in its native order. -/
theorem Wiring.read_message_padding (hw : 0 < w) (i : Fin (L.slack (blockOf u v hne))) :
    let b := blockOf u v hne
    readings m (physicalBitAddress u.val (R+1) (G.program.length+t) link v.val
      (L.header + (legLoad L.three L.width b.val.1 b.val.2 +
        (legLoad L.three L.width b.val.2 b.val.1 + i.val)))) =
      ((L.exteriorEquiv ext).padding ⟨b,i⟩).toNat :=
  G.read_message_region L u v hne pin ext ibase hbase starbase m physical hw (.inr (.inr (.inr i)))

/-- With the genuine prefix and total tables installed, the processor at the specified
endpoint reads exactly its oriented hop. The same physical word is visible to its relay. -/
theorem Wiring.read_message_leg (hw : 0 < w) {endpoint relay : Fin (R+1)}
    (p : Hop L.three L.width endpoint relay)
    (shared : blockOf u v hne = blockOf endpoint relay (hop_ne_relay p))
    (pub : Arg → ℕ) (tab : AddressTables L.three L.width pub (readings m))
    (head : frameField pub (readings m) 5 = L.header) :
    readings m (physicalBitAddress u.val (R+1) (G.program.length+t) link v.val
      (legPosition pub (readings m) endpoint relay p.1 (p.2.val / ((R+1)-2)))) =
      ((L.exteriorEquiv ext).hop endpoint relay p).toNat := by
  rw [tab.legPosition_eq p, head]
  rcases lt_or_gt_of_ne (hop_ne_relay p) with huv | hvu
  · let b : Block (R+1) := ⟨(endpoint,relay),huv⟩
    have hslot : blockOf endpoint relay (hop_ne_relay p) = b := by simp [blockOf,b,huv]
    have hread := G.read_exterior_val hw u v hne pin ext ibase hbase starbase m physical
      (L.position b (.inr (.inl p)))
    rw [shared, hslot] at hread
    have he := congrArg Bool.toNat (exterior_region L ext b (.inr (.inl p)))
    change _ = ((L.exteriorEquiv ext).hop endpoint relay p).toNat at he
    simpa only [L.position_low, b, ite_eq_right (not_lt_of_gt huv), Nat.add_zero, Nat.zero_add, Nat.add_comm] using hread.trans he
  · let b : Block (R+1) := ⟨(relay,endpoint),hvu⟩
    have hslot : blockOf endpoint relay (hop_ne_relay p) = b := by simp [blockOf,b,not_lt_of_gt hvu]
    have hread := G.read_exterior_val hw u v hne pin ext ibase hbase starbase m physical
      (L.position b (.inr (.inr (.inl p))))
    rw [shared, hslot] at hread
    have he := congrArg Bool.toNat (exterior_region L ext b (.inr (.inr (.inl p))))
    change _ = ((L.exteriorEquiv ext).hop endpoint relay p).toNat at he
    simpa only [L.position_high, b, ite_eq_left hvu, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hread.trans he

end TeamContraction

end BorderVNP
end Computability
end OAI
