import OAI.Hierarchy.DescentOrdinaryMaterialParentRoom

namespace OAI
/-! Decode every field of one physically admitted old parent from its two true rooted paths. -/
namespace Hierarchy.DescentRawCablePanel.DepotRAM.Material
open DescentSixParty.Chronology DescentParallelBase.ParentFilter DescentSIMDLookup DescentSharedCableNames
open DescentHaloWalkRAM DescentHaloPackedRebase
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable (s : Shape) (u : Setup) (v : Parts s) (z : Seat s)
local notation "D" => s.degree
local notation "P" => breadth D
local notation "d" => seatDonor s u.profile u.motifWidth u.slots v z.1 z.2.1
local notation "mass" => liveMass (report u.oldBits u.gain u.slots d z.2.2)
local notation "pathAt" side:max => atSeat s u.profile u.motifWidth u.slots side v z.1 z.2.1 z.2.2
local notation "low" side:max => (roleLow u.oldBits u.gain u.slots side d z.2.2).val
local notation "seq" => (z.1.val*s.cap+z.2.1.val)*11+z.2.2.val
local notation "upper" => decide (ranked s v.chart (pathAt true)*u.hostPitch+low true <
                                   ranked s v.chart (pathAt false)*u.hostPitch+low false)

theorem parent_missing {Q K L : ℕ} (rev : Cell (chartBits s)) (fit : ParentRoom s u v rev z Q K L)
    (blank : mass=0) : parent s u v rev z fit=none:=by simp [parent,observations,blank]

theorem parent_emitted {H Q K L : ℕ} (R : Fin H→Fin D→Option (Fin H)) (h : Fin H)
    (fit : ParentRoom s u v (digest (reverseEntries s R h)) z Q K L)
    (left right : Fin P) (src : pathAt false=Packed.token (some left))
    (dst : pathAt true=Packed.token (some right)) (active : mass≠0)
    (pathWidth : P<2^u.fieldBits) (ticketWidth : (P+1)*roles s≤2^u.fieldBits) :
    ∃r, parent s u v (digest (reverseEntries s R h)) z fit=some r ∧
      r.src.path=left ∧ r.dst.path=right ∧ r.src.low.val=low false ∧ r.dst.low.val=low true ∧
      r.weight.val=mass ∧ r.upper=upper ∧
      r.ticket.val=Rebase.value R .rank h left*roles s+seq :=by
  have lpos:(pathAt false).val=left.val+1:=congrArg Fin.val src
  have rpos:(pathAt true).val=right.val+1:=congrArg Fin.val dst
  have read:=fun f=>show observations s u v z f=
    ![left.val+1,right.val+1,low false,low true,(upper).toNat,mass,1,seq] f by simp [observations,active,lpos,rpos]
  have live:observations s u v z 6≠0:=by rw [read];exact Nat.one_ne_zero
  unfold parent
  rw [dite_eq_right live]
  refine ⟨_,rfl,Fin.ext ?_,Fin.ext ?_,?_,?_,?_,?_,?_⟩
  · simp [read]
  · simp [read]
  · simp [read]
  · simp [read]
  · simp [read]
  · change decide (observations s u v z 4=1)=upper
    rw [read]
    have flag (value : Bool) : decide (value.toNat=1)=value := by cases value <;> rfl
    exact flag upper
  · change (ticketLaw s u z (digest (reverseEntries s R h)) (observations s u v z 0:ℕ)).val=_
    have orig:(left.val+1:ℕ)<2^u.fieldBits:=by have :=left.isLt;omega
    have pathHit : ((observations s u v z 0 : ℕ) : Cell u.fieldBits).val=left.val+1 := by
      rw [read]
      exact Fin.val_cast_of_lt orig
    rw [ticket_hit s u R h left z _ pathHit]
    have seqFit:seq<roles s:=by
      have t:=z.2.1.isLt
      have x:=z.1.isLt
      have k:=z.2.2.isLt
      have span:=Nat.mul_le_mul_right s.cap x
      unfold roles
      nlinarith
    have bnd:=Rebase.value_le R .rank h left
    rw [←Nat.add_assoc]
    apply Fin.val_cast_of_lt
    apply Nat.lt_of_lt_of_le _ ticketWidth
    nlinarith [Nat.mul_le_mul_right (roles s) bnd,seqFit]

end
end Hierarchy.DescentRawCablePanel.DepotRAM.Material

end OAI
