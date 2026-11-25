import OAI.Hierarchy.TaggedDigitSequence
import OAI.Hierarchy.TaggedPassSockets
import OAI.Hierarchy.TaggedRadixPassCost

namespace OAI
/-! # The native stage at each position of the finite radix schedule -/

namespace Hierarchy.Tagged.Radix
open ThreeFlat Routing SortNetwork RadixStage
open scoped Classical
noncomputable section

private def emptyShell (F : Type*) (p : ℕ) : BitNetwork F p := ⟨0,0,Fin.elim0,Fin.elim0⟩

abbrev scheduledState (a B : ℝ) (h : ℕ) := state h (digitBits a h) (packBits B h)
abbrev scheduledHoles (a B : ℝ) (h n i : ℕ) := (passShapeAt a B h n i).PassHoles (RadixRecord.width h)

private abbrev rawHoles (a B : ℝ) (h i : ℕ) :=
  (rawShape h (digitBits a h) (packBits B h) i).PassHoles (RadixRecord.width h)

private def move {F : Type*} {I O : Type} [Fintype I] [Fintype O] (H : ℕ → Type)
    [∀ j,Fintype (H j)] {i j : ℕ} (e : i = j) (N : Network F I O (H i)) : Network F I O (H j) :=
  e ▸ N

private theorem move_bill {F : Type*} {I O : Type} [Fintype I] [Fintype O] (H : ℕ → Type)
    [∀ j,Fintype (H j)] {i j : ℕ} (e : i = j) (N : Network F I O (H i)) :
    (move (I := I) (O := O) H e N).cells + (move (I := I) (O := O) H e N).internal = N.cells + N.internal := by
  cases e
  rfl

private theorem move_eval {F : Type*} {I O : Type} [CommSemiring F] [Fintype I] [Fintype O]
    (H : ℕ → Type) [∀ j,Fintype (H j)] (wt : ∀ j,(H j→Bool)→F) {i j : ℕ} (e : i = j)
    {N : Network F I O (H i)} {P : (I→Bool) → Prop} {f : (I→Bool) → O→Bool}
    (ok : ComputesOn N (wt i) P f) : ComputesOn (move (I := I) (O := O) H e N) (wt j) P f := by
  cases e
  exact ok

private def program (F : Type*) [Zero F] [One F] (a B : ℝ) (h i : ℕ) :
    Network F (scheduledState a B h i) (scheduledState a B h (i+1)) (rawHoles a B h i) :=
  (rawShape h (digitBits a h) (packBits B h) i).network F (RadixRecord.blank h)
    (RadixRecord.real h) (RadixRecord.dummy h) (RadixRecord.digit h (digitBits a h) i)

private def select {F : Type*} {I O : Type} [Fintype I] [Fintype O] (H : ℕ → Type)
    [∀ j,Fintype (H j)] (i n : ℕ) (N : Network F I O (H i)) : Network F I O (H (min i n)) :=
  if hi : i ≤ n then move (I := I) (O := O) H (Nat.min_eq_left hi).symm N
  else emptyShell F _

private theorem select_eq {F : Type*} {I O : Type} [Fintype I] [Fintype O] (H : ℕ → Type)
    [∀ j,Fintype (H j)] (i n : ℕ) (hi : i ≤ n) (N : Network F I O (H i)) :
    select (I := I) (O := O) H i n N = move (I := I) (O := O) H (Nat.min_eq_left hi).symm N := dite_eq_left hi

private theorem select_bill {F : Type*} {I O : Type} [Fintype I] [Fintype O] (H : ℕ → Type)
    [∀ j,Fintype (H j)] (i n : ℕ) (hi : i ≤ n) (N : Network F I O (H i)) :
    (select (I := I) (O := O) H i n N).cells + (select (I := I) (O := O) H i n N).internal =
      N.cells + N.internal :=
  (congrArg (fun A : Network F I O (H (min i n)) => A.cells + A.internal)
    (select_eq (I := I) (O := O) H i n hi N)).trans (move_bill (I := I) (O := O) H _ N)

private theorem select_eval {F : Type*} [CommSemiring F] {I O : Type} [Fintype I] [Fintype O] (H : ℕ → Type)
    [∀ j,Fintype (H j)] (wt : ∀ j,(H j→Bool)→F) (i n : ℕ) (hi : i ≤ n)
    (N : Network F I O (H i)) (P : (I→Bool) → Prop) (f : (I→Bool) → O→Bool)
    (ok : ComputesOn N (wt i) P f) :
    ComputesOn (select (I := I) (O := O) H i n N) (wt (min i n)) P f :=
  (congrArg (fun A : Network F I O (H (min i n)) => ComputesOn A (wt (min i n)) P f)
    (select_eq (I := I) (O := O) H i n hi N)).mpr (move_eval (I := I) (O := O) H wt _ ok)

/-- Each meaningful stage is the real six-part pass, with its unclamped
array of output rows. Indices beyond the requested sequence have no cells. -/
def scheduledNetwork (F : Type*) [Zero F] [One F] (a B : ℝ) (h n i : ℕ) :
    Network F (scheduledState a B h i) (scheduledState a B h (i+1)) (scheduledHoles a B h n i) :=
  select (I := scheduledState a B h i) (O := scheduledState a B h (i+1)) (rawHoles a B h) i n (program F a B h i)

set_option maxHeartbeats 1000000 in
theorem scheduled_cost {a B : ℝ} {h n : ℕ} (F : Type*) [Zero F] [One F]
    (two : 2 ≤ h) (g : GridScales a B h) (count : n+1 ≤ 2^(passBits h)) (i : ℕ) (hi : i ≤ n) :
    (scheduledNetwork F a B h n i).cells + (scheduledNetwork F a B h n i).internal +
      Fintype.card (scheduledState a B h (i+1)) ≤ 6000000000000*(2^h*h) := by
  let charge (j : ℕ) :=
    let s := rawShape h (digitBits a h) (packBits B h) j
    let N := s.network F (RadixRecord.blank h) (RadixRecord.real h) (RadixRecord.dummy h)
      (RadixRecord.digit h (digitBits a h) i)
    N.cells + N.internal + Fintype.card (RowBits s.nextRows (RadixRecord.width h))
  have bill : charge (min i n) ≤ 6000000000000*(2^h*h) :=
    g.pass_network_cost two count (show RadixRecord.width h ≤ 4*h by unfold RadixRecord.width; omega) F i
      (RadixRecord.blank h) (RadixRecord.real h) (RadixRecord.dummy h) (RadixRecord.digit h (digitBits a h) i)
  have atIndex : charge i ≤ 6000000000000*(2^h*h) := (congrArg charge (Nat.min_eq_left hi)) ▸ bill
  have sizes := select_bill (I := scheduledState a B h i) (O := scheduledState a B h (i+1)) (rawHoles a B h) i n hi (program F a B h i)
  exact (Nat.add_le_add_right sizes.le _).trans atIndex

set_option maxHeartbeats 1000000 in
theorem scheduled_computes {a B : ℝ} {h n : ℕ} (F : Type*) [CommSemiring F] (i : ℕ) (hi : i ≤ n)
    (ok : let s := rawShape h (digitBits a h) (packBits B h) i
      ComputesOn (s.network F (RadixRecord.blank h) (RadixRecord.real h) (RadixRecord.dummy h) (RadixRecord.digit h (digitBits a h) i))
        (PassShape.weight F s (RadixRecord.width h)) allowed (rawRun h (digitBits a h) (packBits B h) i)) :
    ComputesOn (scheduledNetwork F a B h n i) (PassShape.weight F (passShapeAt a B h n i) (RadixRecord.width h))
      allowed (rawRun h (digitBits a h) (packBits B h) i) := by
  let wt (j : ℕ) := PassShape.weight F (rawShape h (digitBits a h) (packBits B h) j) (RadixRecord.width h)
  have checked : ComputesOn (program F a B h i) (wt i) allowed (rawRun h (digitBits a h) (packBits B h) i) := ok
  exact select_eval (I := scheduledState a B h i) (O := scheduledState a B h (i+1)) (rawHoles a B h) wt i n hi
    (program F a B h i) allowed (rawRun h (digitBits a h) (packBits B h) i) checked

end
end Hierarchy.Tagged.Radix

end OAI
