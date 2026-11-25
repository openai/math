import OAI.Hierarchy.ProbeStageAdviceSize

namespace OAI
/-! # Disjoint address ranges across subdivision levels -/

namespace Hierarchy.ProbeStage.Native

/-- Number of banks required by one level. The parameter counts the
simultaneously live copies of the occurrence and counter stores. -/
def stride (d copies : ℕ) := 32+copies*(288*d+17)
def extent (h d : ℕ) := 2^roomBits h d

/-- Three initial banks hold the singleton group and permutation endpoints.
Each subsequent level has its own rank, advice, counter and output space. -/
def phase (h d copies j : ℕ) := (3+j*stride d copies)*extent h d
def bankBase (h d copies j bank : ℕ) := phase h d copies j + bank*extent h d
def output (h d copies j : ℕ) := bankBase h d copies j (stride d copies-9)
def heapEnd (h d copies : ℕ) := phase h d copies (rounds d)

theorem phase_succ (h d copies j : ℕ) :
    phase h d copies (j+1) = phase h d copies j+stride d copies*extent h d := by
  unfold phase
  ring

theorem separate (h d copies j i k : ℕ) (hik : i<k) :
    bankBase h d copies j i+extent h d ≤ bankBase h d copies j k := by
  have mul := Nat.mul_le_mul_right (extent h d) (show i+1≤k by omega)
  rw [Nat.succ_mul] at mul
  dsimp [bankBase]
  omega

theorem mask_storage {h d j : ℕ} (hd : 1≤d) (hj : j≤rounds d) (copies : ℕ) :
    let B := radix h d
    let words := B^j*blocks (2^widthLog h d j) B*(B^4*(8*(4*h+2))+B)
    bankBase h d copies j 14 + copies*words ≤ output h d copies j := by
  have current := occurrences_at_depth (h:=h) hd hj
  have level : 4^j*2^h ≤ extent h d := by
    rw [extent,room_slots]
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by omega))
  rw [Nat.mul_assoc (288*d+17)] at current
  have bound := current.trans (Nat.mul_le_mul_left (288*d+17) level)
  have c := Nat.mul_le_mul_left copies bound
  change _+copies*_≤_
  rw [output,bankBase,bankBase]
  rw [Nat.add_assoc]
  apply Nat.add_le_add_left
  have diff : stride d copies-9=23+copies*(288*d+17) := by unfold stride;omega
  rw [diff,Nat.add_mul]
  simp only [Nat.mul_assoc] at c ⊢
  omega

/-- All nine emitted dense columns are inside the current level's area. -/
theorem output_end (h d copies j : ℕ) :
    output h d copies j+9*(2^h) ≤ phase h d copies (j+1) := by
  have cap : 2^h≤extent h d := Nat.pow_le_pow_right (by decide) (by unfold roomBits;omega)
  have a := Nat.mul_le_mul_left 9 cap
  have diff : stride d copies-9+9=stride d copies := by unfold stride;omega
  rw [phase_succ,output,bankBase]
  have full := congrArg (fun u => u*extent h d) diff
  rw [Nat.add_mul] at full
  omega

theorem phase_in_heap {h d copies i : ℕ} (hi : i≤rounds d) :
    phase h d copies i≤heapEnd h d copies := by
  exact Nat.mul_le_mul_right _ (Nat.add_le_add_left (Nat.mul_le_mul_right _ hi) _)

/-- The second height-sized part of a word leaves room for any fixed linear
amount of caller workspace adjoining the subdivision tape. -/
def wordBits (h d copies : ℕ) := roomBits h d + (3+rounds d*stride d copies)+h

theorem wordBits_linear (h d copies : ℕ) :
    wordBits h d copies=2*h+(2*(rounds d+1)+3+rounds d*stride d copies) := by
  unfold wordBits roomBits
  omega

private theorem base_room (h d copies : ℕ) :
    heapEnd h d copies < 2^(roomBits h d+(3+rounds d*stride d copies)) := by
  let c := 3+rounds d*stride d copies
  have cap : c<2^c := Nat.lt_two_pow_self
  have pos : 0<extent h d := pow_pos (by decide) _
  change c*extent h d < 2^(roomBits h d+c)
  rw [pow_add,Nat.mul_comm]
  exact Nat.mul_lt_mul_of_pos_left cap pos

theorem heap_room (h d copies : ℕ) : heapEnd h d copies < 2^wordBits h d copies :=
  (base_room h d copies).trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))

theorem append_room {h d copies K : ℕ} (enough : K+1≤2^h) :
    heapEnd h d copies+K*2^h<2^wordBits h d copies := by
  let b := 2^(roomBits h d+(3+rounds d*stride d copies))
  have start : heapEnd h d copies<b := base_room h d copies
  have nr : 2^h≤b := Nat.pow_le_pow_right (by decide) (by unfold roomBits;omega)
  have m := Nat.mul_le_mul_left K nr
  have limit := Nat.mul_le_mul_right b enough
  rw [Nat.succ_mul] at limit
  change _<2^(roomBits h d+(3+rounds d*stride d copies)+h)
  rw [pow_add]
  change _<b*2^h
  rw [Nat.mul_comm b (2^h)]
  omega

theorem eventually_append_room (d copies K : ℕ) :
    ∀ᶠ h : ℕ in Filter.atTop,heapEnd h d copies+K*2^h<2^wordBits h d copies := by
  exact Filter.eventually_atTop.2 ⟨K+1,fun h hh => append_room (hh.trans (Nat.lt_two_pow_self.le))⟩

theorem heap_words (h d copies : ℕ) :
    heapEnd h d copies = (3+rounds d*stride d copies)*4^(rounds d+1)*2^h := by
  rw [heapEnd,phase,extent,room_slots,Nat.mul_assoc]

end Hierarchy.ProbeStage.Native

end OAI
