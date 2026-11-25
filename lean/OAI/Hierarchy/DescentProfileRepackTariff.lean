import OAI.Hierarchy.DescentOriginalPitchPages
import OAI.Hierarchy.DescentPackedEpochBill
import OAI.Hierarchy.DescentPackedProfileRepackNative

namespace OAI
/-! # Cost of reading the original shelf and installing the selected matcher's raw input -/
namespace Hierarchy.DescentPackedProfileRepack
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM

set_option maxRecDepth 8192 in
theorem original_tariff (base seats A B b d w payload H : ℕ) (source raw : Bank)
    (oldPos : 0<A) (newPos : 0<B) (large : 64≤payload)
    (oldPitch : A≤payload) (newPitch : B≤payload) (oldBits : b*A≤payload/4) (newBits : b*B≤payload/2)
    (pages : 2^(payload/2)≤H) :
    ticks base seats A B b source raw+7*DescentStaticWordColumn.names (program base seats A B b d source raw w)≤
      4096*(H+chunks seats A+chunks seats B+raw.size+1) := by
  have dict:=(Overlap.original_pages payload seats A B b large oldPitch newPitch oldBits).trans pages
  have widen : 2^(b*B)≤H := (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) newBits).trans pages
  have sum:=tariff base seats A B b d source raw w oldPos newPos
  simp only [Overlap.rows,one_mul] at sum
  omega

theorem common_pitch_tariff (base seats B b d w payload H : ℕ) (source raw : Bank)
    (oldPos : 0<lanes (payload/2) b) (newPos : 0<B) (large : 64≤payload)
    (newPitch : B≤payload) (newBits : b*B≤payload/2) (pages : 2^(payload/2)≤H) :
    let A:=lanes (payload/2) b
    ticks base seats A B b source raw+7*DescentStaticWordColumn.names (program base seats A B b d source raw w)≤
      4096*(H+chunks seats A+chunks seats B+raw.size+1) := by
  dsimp only
  exact original_tariff base seats _ B b d w payload H source raw oldPos newPos large
    ((Nat.div_le_self ..).trans (Nat.div_le_self ..)) newPitch (Overlap.original_header_bits ..) newBits pages


/-- The paid calendar uses a common header with one extra tag bit and its chosen wider pitch.
Each physical RAM word pays for the selector seats it carries at the old or new lane width. -/
theorem header_invoice (base seats B C d w payload H newUnit ratio : ℕ) (source raw : Bank)
    (large : 64≤payload) (headerRate : 2*DescentPackedEpochShelves.unit C≤payload/2)
    (newPos : 0<B) (newShort : B≤payload) (newBits : DescentTerminalEpochBits.width C*B≤payload/2)
    (newRate : payload≤4*B*newUnit) (pages : 2^(payload/2)≤H)
    (padding : raw.size≤2*(seats/B+2)) (width : w≤ratio*payload) :
    let A:=DescentPackedEpochShelves.grain (payload/2) C
    let b:=DescentTerminalEpochBits.width C
    (ticks base seats A B b source raw+7*DescentStaticWordColumn.names (program base seats A B b d source raw w))*w≤
      131072*ratio*(H*payload+seats*(DescentPackedEpochShelves.unit C+newUnit)) := by
  let U:=DescentPackedEpochShelves.unit C
  let A:=DescentPackedEpochShelves.grain (payload/2) C
  let b:=DescentTerminalEpochBits.width C
  have up : 0<U := Nat.zero_lt_succ _
  obtain ⟨aPos,filled⟩:=occupancy (payload/2) U up headerRate
  change 0<A at aPos
  change payload/2≤4*A*U at filled
  have bU : b≤U:=Nat.le_succ _
  have original : b*A≤payload/4 :=
    (Nat.mul_le_mul_right A bU).trans (Overlap.original_header_bits payload U)
  have aShort : A≤payload := (Nat.div_le_self ..).trans (Nat.div_le_self ..)
  have billed:=original_tariff base seats A B b d w payload H source raw aPos newPos large aShort newShort original newBits pages
  have positive : 0<8*A*U:=Nat.mul_pos (Nat.mul_pos (by decide) aPos) up
  have oldRate : payload≤12*A*U:=by nlinarith only [filled,show payload≤2*(payload/2)+1 by omega,positive]
  have old:=Overlap.floor_bill seats A payload 12 U oldRate
  have newCost:=Overlap.floor_bill seats B payload 4 newUnit newRate
  have ca:=(Nat.mul_le_mul_right payload (Overlap.chunks_floor seats A aPos))
  have cb:=(Nat.mul_le_mul_right payload (Overlap.chunks_floor seats B newPos))
  have rawCost:=Nat.mul_le_mul_right payload padding
  have fixed : payload≤H*payload := by
    have one : 1≤H:=(Nat.two_pow_pos _).trans_le pages
    simpa only [one_mul] using Nat.mul_le_mul_right payload one
  have measured:=Nat.mul_le_mul_right payload billed
  have endBound : (ticks base seats A B b source raw+7*DescentStaticWordColumn.names
      (program base seats A B b d source raw w))*payload≤131072*(H*payload+seats*(U+newUnit)) := by
    nlinarith only [measured,ca,cb,rawCost,old,newCost,fixed]
  calc
    _ ≤ _*(ratio*payload) := Nat.mul_le_mul_left _ width
    _ = ratio*(_*payload) := by ring
    _ ≤ ratio*(131072*(H*payload+seats*(U+newUnit))) := Nat.mul_le_mul_left _ endBound
    _ = _ := by ring

end Hierarchy.DescentPackedProfileRepack

end OAI
