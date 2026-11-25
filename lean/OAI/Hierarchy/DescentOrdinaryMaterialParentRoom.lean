import OAI.Hierarchy.DescentOrdinaryMaterialParent

namespace OAI
/-! Paths and canonical parent tickets fit the public alphabet even on the padded donor board. -/
namespace Hierarchy.DescentRawCablePanel.DepotRAM.Material
open DescentSixParty.Chronology DescentSIMDLookup DescentHaloWalkRAM DescentSharedCableNames DescentHaloPackedRebase DescentPacking.PackedMatch.Local
open scoped Classical Fin.CommRing
noncomputable section
variable (s : Shape) (u : Setup) (v : Parts s) (z : Seat s)
local notation "P₀"=>breadth s.degree
local notation "read₀"=>observations s u v z

private theorem path_le (side : Bool) :
    (atSeat s u.profile u.motifWidth u.slots side v z.1 z.2.1 z.2.2).val≤P₀:=by
  rw [seat_read]
  simp only [ParentIncidence.paths,Equiv.symm_apply_apply]
  unfold ParentIncidence.pathCell
  split
  · simp
  · rename_i p _
    exact (ActorPath.index s.degree (if side then p.2 else p.1)).isLt

theorem previous_paths : read₀ 0≤P₀ ∧ read₀ 1≤P₀:=by
  unfold observations
  split
  · simp
  · exact ⟨path_le s u v z false,path_le s u v z true⟩

theorem previous_ticket {H:ℕ} (R : Fin H→Fin s.degree→Option (Fin H)) (h : Fin H) (path : Cell u.fieldBits) :
    (ticketLaw s u z (digest (reverseEntries s R h)) path).val<(P₀+1)*roles s :=by
  have seats: 0<roles s:=(seatIndex s z).pos
  by_cases live : 0<path.val ∧ path.val≤P₀
  · let p : Fin P₀:=⟨path.val-1,by omega⟩
    have eqn : path.val=p.val+1:=by dsimp [p];omega
    rw [ticket_hit s u R h p z path eqn]
    have rid:=Rebase.value_le R .rank h p
    have low :(z.1.val*s.cap+z.2.1.val)*11+z.2.2.val<roles s :=by
      have col : z.1.val*s.cap+z.2.1.val < s.blocks*s.cap := by
        calc
          _ < (z.1.val+1)*s.cap := by rw [Nat.add_mul, Nat.one_mul]; omega
          _ ≤ _ := Nat.mul_le_mul_right _ z.1.isLt
      unfold roles
      calc
        _ < ((z.1.val*s.cap+z.2.1.val)+1)*11 := by omega
        _ ≤ (s.blocks*s.cap)*11 := Nat.mul_le_mul_right _ col
        _ = _ := Nat.mul_assoc _ _ _
    have span:=Nat.mul_le_mul_right (roles s) rid
    change _%2^u.fieldBits<_
    apply lt_of_le_of_lt (Nat.mod_le _ _)
    calc
      _ = Rebase.value R .rank h p * roles s + ((z.1.val*s.cap+z.2.1.val)*11+z.2.2.val) := by omega
      _ < breadth s.degree * roles s + roles s := Nat.add_lt_add_of_le_of_lt span low
      _ = _ := (Nat.succ_mul _ _).symm
  · simp only [ticketLaw,dite_eq_right live,Fin.val_zero]
    positivity

theorem parent_room {H Q K L : ℕ} (R : Fin H→Fin s.degree→Option (Fin H)) (h : Fin H)
    (tickets : (P₀+1)*roles s≤K)
    (low : ∀t:Fin 2, read₀ 6≠0→(roleLow u.oldBits u.gain u.slots (decide (t.val=1))
      (seatDonor s u.profile u.motifWidth u.slots v z.1 z.2.1) z.2.2).val<Q)
    (mass : read₀ 6≠0→liveMass (report u.oldBits u.gain u.slots
      (seatDonor s u.profile u.motifWidth u.slots v z.1 z.2.1) z.2.2)≤L) :
    ParentRoom s u v (digest (reverseEntries s R h)) z Q K L :=by
  obtain ⟨left,right⟩:=previous_paths s u v z
  refine ⟨fun h=>⟨left,?_⟩,fun h=>⟨right,?_⟩,fun h=>?_,fun _=>(previous_ticket s u z R h _).trans_le tickets⟩
  · have q:=low 0 h
    unfold observations at h ⊢
    split at h <;> simp_all
  · have q:=low 1 h
    unfold observations at h ⊢
    split at h <;> simp_all
  · have q:=mass h
    unfold observations at h ⊢
    split at h <;> simp_all

end
end Hierarchy.DescentRawCablePanel.DepotRAM.Material

end OAI
