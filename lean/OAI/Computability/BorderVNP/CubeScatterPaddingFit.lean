import OAI.Computability.BorderVNP.CubeScatterPaddingTail

/-! # Word bounds for the true physical padding scan

The used-width cap and the two actual reserved bank extents bound every
executed address calculation. Packet divisors are needed only inside a
nonempty suffix.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Padding

open Physical Physical.Owned HostAddress HostScatter Tally VPVNP.MotifBase
open private key_lt key_surj from OAI.Computability.BorderVNP.CubeScatterPaddingTail

variable {Team : Type*} {n d blocks b h K s w : ℕ} {i : Fin (n+1)} {group : Fin d → Team}
  {number : Team ↪ ℕ} {t : Team} {l : Layout} {mem used : ℕ → ℕ}

/-- Extents of the actual allocated arrays at word width w. -/
structure PhysicalRoom (l : Layout) (w n d blocks b h K s : ℕ) : Prop where
  /-- Unsigned terminal pair counter. -/
  pairs : l.count < 2^w
  /-- The entire common stride fits as one computed word. -/
  stride : blocks*(h*b) < 2^w
  /-- One owner word per alphabet symbol. -/
  owners : l.owners+d ≤ 2^w
  /-- One occupied width per product pair. -/
  widths : l.widths+l.count ≤ 2^w
  /-- Three packet-address fields per product pair. -/
  triples : l.triples+3*l.count ≤ 2^w
  /-- Full uniform singleton reservation. -/
  singles : l.singles+d^(n+1)*d^(n+1)*(blocks*(h*b)) ≤ 2^w
  /-- Full globally indexed packet reservation. -/
  packets : l.packets+(d*d)^(n+1)*2*blocks*bankWidth n b h K s ≤ 2^w

private theorem physical_address_lt (room : PhysicalRoom l w n d blocks b h K s)
    (u v : Label (n+1) d) (j : Fin (blocks*(h*b))) (side : Bool) :
    address d (n+1) blocks (h*b) l.packets (bankWidth n b h K s) (selectorWidth n K h)
      l.singles (code u) (code v) j.val side < 2^w := by
  rw [address_eq_split]
  cases e : splitSlot n d blocks (h*b) ((u,v),j) with
  | inr z =>
    have lim := Nat.mul_le_mul_right (blocks*(h*b)) (key_lt z.1.val.1 z.1.val.2)
    rw [Nat.succ_mul] at lim
    have jj := z.2.isLt
    have fit := room.singles
    simp only
    omega
  | inl z =>
    obtain ⟨p,x,k⟩ := z
    let sym := p.1.1 (0 : Fin (n+1))
    let trial := (packetRowEquiv 0 sym).symm ⟨p,rfl⟩
    have he : (packetRowEquiv 0 sym trial).val = p := congrArg Subtype.val (Equiv.apply_symm_apply ..)
    have hi := trialPacketIndex_lt 0 sym trial.val
    rw [trialPacketIndex_eq 0 sym trial,he] at hi
    have lim := Nat.mul_le_mul_right (bankWidth n b h K s) hi
    rw [Nat.succ_mul] at lim
    have slot := (demandOffset_range (K := K) (x,side) k).2
    have bound : demandOffset n b h K (x,side) k < bankWidth n b h K s := by unfold bankWidth; omega
    have fit := room.packets
    simp only
    omega

/-- Every actual native word and bit-source address fits, derived from the true
pair-directory readout, the occupied-width cap and the physical bank allocation. -/
theorem TailHeader.fits_of_room (header : TailHeader i group number t l mem used blocks b h K s)
    (hd : 0 < d) (room : PhysicalRoom l w n d blocks b h K s)
    (occupied : ∀ k < l.count, used k ≤ blocks*(h*b)) : l.Fits w mem := by
  have stride : l.stride = blocks*(h*b) := by simp [Layout.stride,header.banks.1,header.banks.2.1]
  have widths (k : ℕ) (hk : k < l.count) : mem (l.widths+k) ≤ l.stride := by
    rw [header.widths k hk,stride]
    exact occupied k hk
  refine ⟨header.alphabet.2.1 ▸ hd,header.alphabet.2.2 ▸ pow_pos hd _,header.alphabet.1 ▸ pow_pos hd _,
    room.pairs,stride ▸ room.stride,?_,?_,?_,widths,?_⟩
  · intro k _ side
    have modlt := Nat.mod_lt (l.label k side / l.place) (header.alphabet.2.1 ▸ hd : 0 < l.groups)
    exact (Nat.add_lt_add_left modlt _).trans_le (header.alphabet.2.1 ▸ room.owners)
  · intro k hk; exact (Nat.add_lt_add_left hk _).trans_le room.widths
  · intro k hk; have := room.triples; omega
  · intro k hk side _
    obtain ⟨u,v,rfl⟩ := key_surj (show k < d^(n+1)*d^(n+1) by simpa [Layout.count,header.alphabet.1] using hk)
    let key := code u*d^(n+1)+code v
    let f := l.fields mem key side
    have start : f.start = used key := header.widths key hk
    have width : f.width = blocks*(h*b)-used key := by
      simp [f,Layout.fields,header.widths key hk,stride]
    have cap := occupied key hk
    have src (j : ℕ) (hj : j < f.width) : f.source j < 2^w := by
      rw [width] at hj
      let ord : Fin (blocks*(h*b)) := ⟨used key+j,by omega⟩
      exact (header.source_eq u v side j).trans_lt (physical_address_lt room u v ord side)
    have bc : f.bc = h*b := header.banks.2.1
    have positive (hw : 0 < f.width) : 0 < f.bc := by
      rw [width] at hw; rw [bc]; by_contra! zero; simp [Nat.eq_zero_of_le_zero zero] at hw
    change f.Fits w
    refine ⟨?_,?_,fun _ => ?_,fun _ hw => positive hw,?_,?_,src⟩
    · rw [start,width]; have := room.stride; omega
    · change 0+f.width ≤ 2^w; rw [width]; have := room.stride; omega
    · change l.stride < 2^w; rw [stride]; exact room.stride
    · intro j hj packet
      have bound := src j hj
      rw [BitFields.source,ite_eq_right packet] at bound
      have pos : 0 < bankWidth n b h K s := by
        have q := (demandOffset_range (K := K) ((0 : Vertex n),false) (⟨0,bc ▸ positive (Nat.zero_lt_of_lt hj)⟩ : Fin (h*b))).2
        unfold bankWidth; omega
      have bw : f.bankWidth = bankWidth n b h K s := header.banks.2.2.1
      have le := Nat.le_mul_of_pos_right (f.first+(f.start+j)/f.bc) (bw ▸ pos : 0 < f.bankWidth)
      omega
    · intro packet hw
      have bound := src 0 hw
      rw [BitFields.source,ite_eq_right packet] at bound
      have le := Nat.le_mul_of_pos_right (2*f.vertex+f.side) (positive hw)
      omega

end Cube.Padding

end BorderVNP
end Computability
end OAI
