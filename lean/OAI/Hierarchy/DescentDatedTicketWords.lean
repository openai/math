import OAI.Hierarchy.DescentTicketFragment

namespace OAI
/-! # The original side and role cells encoded by the eight native ticket words -/
namespace Hierarchy.DescentDatedPublicGrain
open DescentSIMDLookup DescentPriorOperandColumns
/-- The first five fields follow the chosen donor and child. The sixth is fixed
at the date, including on private, captured, external, and unsplit jobs. -/
def withGrain {k : ℕ} (grain : Cell (k+2)) (s : Side k) : Side k := {s with grain:=grain}

end Hierarchy.DescentDatedPublicGrain

namespace Hierarchy.DescentDatedOperandCoordinates.Ticket
open scoped Fin.CommRing
open DescentSIMDLookup DescentPriorOperandColumns
noncomputable section

def recordedSide (size : ℕ) (words : Fin 8 → ℕ) : Side size :=
  ⟨(words 0:ℕ),decide (words 1=1),decide (words 2=1),decide (words 3=1),(words 4:ℕ),0⟩
def recordedRole (size : ℕ) (words : Fin 8 → ℕ) (f : Fin 3) : Cell (size+2) :=
  (words ⟨5+f.val,by have:=f.isLt;omega⟩:ℕ)

/-- Only the two capture fields and the signed mark are boolean. The other five
words retain their original packed cell, including a legitimate zero private donor. -/
structure Flags (word : Fin 8 → ℕ) : Prop where
  first : word 1≤1
  second : word 2≤1
  marked : word 3≤1

end
end Hierarchy.DescentDatedOperandCoordinates.Ticket

namespace Hierarchy.DescentDatedOperandReadPipeline
open scoped Classical Fin.CommRing

def postedVector (donor : ℕ) (first second marked : Bool) (start peer ordinal role : ℕ) : Fin 8→ℕ :=
  ![if first || second then donor else 0,first.toNat,second.toNat,marked.toNat,
    if first || second then 0 else start,if first || second then 0 else peer,ordinal,role]

theorem postedVector_eq (donor : ℕ) (first second marked : Bool) (start peer ordinal role : ℕ) :
    let got:=first.toNat≠0 ∨ second.toNat≠0
    postedVector donor first second marked start peer ordinal role=
      ![if got then donor else 0,first.toNat,second.toNat,marked.toNat,
        if got then 0 else start,if got then 0 else peer,ordinal,role] :=by
  cases first <;> cases second <;> rfl

end Hierarchy.DescentDatedOperandReadPipeline

end OAI
