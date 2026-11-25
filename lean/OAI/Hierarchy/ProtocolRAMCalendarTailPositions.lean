import OAI.Hierarchy.ProtocolRAMCalendarArena
import OAI.Hierarchy.ProtocolRAMCalendarTailLists

namespace OAI
/-! # Ordinals of archived decisions against the following chronological blocks -/
namespace Hierarchy.ProtocolRAM.Calendar

private theorem reserve_lower (c : Mesh) (p h j : ℕ) {e : Event} (he : e∈reserveBlock c p h j) :
    sliceBase c p h j≤position c e := by
  have pos := List.mem_map_of_mem (f:=position c) he
  rw [reserve_positions,List.mem_range'_1] at pos
  exact pos.1

private theorem trial_lower (c : Mesh) (p h : ℕ) {e : Event} (he : e∈trialBlock c p h) :
    trialBase c p h≤position c e := by
  have pos := List.mem_map_of_mem (f:=position c) he
  rw [trial_positions,List.mem_range'_1] at pos
  exact pos.1

private theorem phase_lower (c : Mesh) (p : ℕ) {e : Event} (he : e∈outerBlock c p) :
    p*phaseSize c≤position c e := by
  have pos := List.mem_map_of_mem (f:=position c) he
  rw [phase_positions,List.mem_range'_1] at pos
  exact pos.1

theorem trialTail_after (c : Mesh) (p h extra : ℕ) (e : Event) (he : e∈trialTail c p h extra) :
    position c (.attempt (.outer p h))<position c e := by
  rcases List.mem_append.mp he with prior|rest
  · obtain ⟨j,_,inside⟩:=List.mem_flatMap.mp prior
    have lo:=reserve_lower c p h j inside
    change trialBase c p h<_
    unfold sliceBase at lo
    omega
  · obtain ⟨u,bounds,inside⟩:=List.mem_flatMap.mp rest
    obtain ⟨t,_,rfl⟩:=List.mem_map.mp bounds
    apply lt_of_lt_of_le ?_ (trial_lower c p _ inside)
    change _+h*trialSize c<_+(h+1+t)*trialSize c
    apply Nat.add_lt_add_left
    exact Nat.mul_lt_mul_of_pos_right (by omega) (by unfold trialSize;omega)

theorem phaseTail_after (c : Mesh) (p h extra b : ℕ) (hh : h<c.outerFuel) (e : Event)
    (he : e∈phaseTail c p h extra b) : position c (.attempt (.outer p h))<position c e := by
  have guard : trialBase c p h<p*phaseSize c+c.outerFuel*trialSize c :=
    Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_right hh (by unfold trialSize;omega)) _
  have ahead (t : ℕ) : trialBase c p h<(p+1+t)*phaseSize c := by
    apply lt_of_lt_of_le ?_ (Nat.mul_le_mul_right (phaseSize c) (show p+1≤p+1+t by omega))
    rw [Nat.add_mul,Nat.one_mul]
    exact guard.trans (Nat.add_lt_add_left (by unfold phaseSize;omega) _)
  simp only [phaseTail,List.mem_append,List.mem_singleton,or_assoc] at he
  rcases he with prev|rfl|later|last
  · exact trialTail_after c p h _ e prev
  · exact guard
  · obtain ⟨u,ur,hit⟩:=List.mem_flatMap.mp later
    obtain ⟨t,_,rfl⟩:=List.mem_map.mp ur
    exact (ahead t).trans_le (phase_lower c _ hit)
  · obtain ⟨a,_,hit⟩:=List.mem_flatMap.mp last
    exact (ahead extra).trans_le ((Nat.le_add_right _ (a*trialSize c)).trans (trial_lower c _ _ hit))

theorem innerTail_after (c : Mesh) (p h j b extra : ℕ) (e : Event) (he : e∈innerTail p h j b extra) :
    position c (.attempt (.inner p h j b))<position c e := by
  obtain ⟨u,ur,rfl⟩:=List.mem_map.mp he
  obtain ⟨t,_,rfl⟩:=List.mem_map.mp ur
  change sliceBase c p h j+b<sliceBase c p h j+(b+1+t)
  omega

theorem reserveTail_after (c : Mesh) (p h j b extra trial : ℕ) (hb : b<c.innerFuel) (e : Event)
    (he : e∈reserveTail c p h j b extra trial) : position c (.attempt (.inner p h j b))<position c e := by
  have guard : sliceBase c p h j+b<sliceBase c p h j+c.innerFuel := Nat.add_lt_add_left hb _
  have ahead (t : ℕ) : sliceBase c p h j+b<sliceBase c p h (j+1+t) := by
    have le := Nat.mul_le_mul_right (sliceSize c) (show j+1≤j+1+t by omega)
    unfold sliceBase
    rw [Nat.add_mul,Nat.one_mul] at le
    unfold sliceSize at le ⊢
    omega
  simp only [reserveTail,List.mem_append,List.mem_singleton,or_assoc] at he
  rcases he with prev|rfl|later|last
  · exact innerTail_after c p h j b _ e prev
  · exact guard
  · obtain ⟨u,ur,hit⟩:=List.mem_flatMap.mp later
    obtain ⟨t,_,rfl⟩:=List.mem_map.mp ur
    exact (ahead t).trans_le (reserve_lower c _ _ _ hit)
  · obtain ⟨i,_,rfl⟩:=List.mem_map.mp last
    exact (ahead extra).trans_le (Nat.le_add_right _ i)

theorem purchaseTail_after (c : Mesh) (p a j b : ℕ) (e : Event) (he : e∈purchaseTail c p a j b) :
    position c (.attempt (.outer p a))<position c e := by
  rcases List.mem_append.mp he with prior|head
  · obtain ⟨k,_,hk⟩ := List.mem_flatMap.mp prior
    rcases List.mem_append.mp hk with tries|feed
    · obtain ⟨i,_,rfl⟩ := List.mem_map.mp tries
      simp only [position,sliceBase]
      omega
    · obtain rfl := List.mem_singleton.mp feed
      simp only [position,sliceBase]
      omega
  · obtain ⟨i,_,rfl⟩ := List.mem_map.mp head
    simp only [position,sliceBase]
    omega

end Hierarchy.ProtocolRAM.Calendar

end OAI
