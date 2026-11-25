import OAI.ThreeFlat.Diagonal.BlockEvaluation

namespace OAI
/-! # Physical indices for a block which touches a single half of memory

The coordinates give explicit maps and matrix units for the rank argument.
The untouched half is the catalyst. The other half is duplicated in the
coordinate maps: one copy checks the touched chunks, the other enforces the
identity on every unvisited bit. All auxiliary bits belong to the touched
factor.
-/

namespace ThreeFlat.Diagonal

variable {I T A S : Type*} [Fintype T] [DecidableEq I] [DecidableEq S] [Inhabited S]
variable {F : Type*} [Field F]

/-- The two external halves and the auxiliary register. -/
abbrev MachineState (I S A : Type*) := (Bool → I → S) × A

/-- Remove the chunks that are allowed to change. -/
def remainingHalf (slots : Finset I) (x : I → S) (i : I) : S :=
  if i ∈ slots then default else x i

omit [DecidableEq S] in
theorem remainingHalf_eq_iff (slots : Finset I) (x y : I → S) :
    remainingHalf slots x = remainingHalf slots y ↔ ∀ i ∉ slots, x i = y i := by
  constructor
  · intro h i hi
    simpa [remainingHalf, hi] using congrFun h i
  · intro h
    funext i
    by_cases hi : i ∈ slots <;> simp [remainingHalf, hi, h]

/-- Data fixed at the input or output end of a block. -/
abbrev BlockEnd (T S A : Type*) := (T → S) × A

/-- Read the touched values and the auxiliary register at one end. -/
def touchedEnd (atSlot : T → I) (active : Bool) (x : MachineState I S A) : BlockEnd T S A :=
  (x.1 active ∘ atSlot, x.2)

def halfCoordinates (atSlot : T → I) (active : Bool) (x : MachineState I S A) :
    (BlockEnd T S A × (I → S)) × (I → S) :=
  ((touchedEnd atSlot active x, remainingHalf (Finset.univ.image atSlot) (x.1 active)),
    x.1 (!active))

/-- Endpoint test for the touched chunks and auxiliary bits. -/
noncomputable def checkEnd {T S A : Type*} (endpt : BlockEnd T S A) :
    BlockEnd T S A → F := by
  classical
  exact fun a => if a = endpt then 1 else 0

/-- Entry of a fixed summand on the real external and auxiliary indices.
The approximating matrix is evaluated precisely on the two inactive halves. -/
theorem physical_fixing_entry [Fintype I] [Fintype S] [Fintype A] [DecidableEq A] (atSlot : T → I) (active : Bool)
    (before after : BlockEnd T S A) (M : Matrix (I → S) (I → S) F)
    (x y : MachineState I S A) :
    fixingMatrix (halfCoordinates atSlot active) (halfCoordinates atSlot active)
      (checkEnd before) (checkEnd after) M x y =
      if touchedEnd atSlot active x = before ∧ touchedEnd atSlot active y = after ∧
          (∀ i ∉ Finset.univ.image atSlot, x.1 active i = y.1 active i) then
        M (x.1 (!active)) (y.1 (!active)) else 0 := by
  classical
  rw [fixingMatrix_apply]
  simp only [halfCoordinates, remainingHalf_eq_iff, checkEnd]
  split_ifs <;> simp_all; split_ifs <;> simp_all

end ThreeFlat.Diagonal

end OAI
