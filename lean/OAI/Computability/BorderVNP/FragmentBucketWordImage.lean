import OAI.Computability.BorderVNP.FragmentBucketProgram

/-! # Every memory word after the stable fragment bucket

The bucket program writes two header words per cell, three fragment fields
per sorted row, and a cursor per cell. This gives a single computed RAM image
for the following task builder, including the words outside all three tables.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FragmentBucket

open RoutingISA

variable (l : Layout) (tag : Fin l.rows → Fin l.cells) (fields : Fin l.rows → Fin 3 → ℕ)

/-- Complete physical output of the stable bucket, as a function of the input
memory, the directed owner tags and the three actual fragment fields. -/
def Layout.wordImage (before : ℕ → ℕ) (a : ℕ) : ℕ :=
  if h : l.pairs ≤ a ∧ a < l.pairs+2*l.cells then
    let c : Fin l.cells := ⟨(a-l.pairs)/2,by omega⟩
    if (a-l.pairs)%2=0 then start tag c.val else count tag c
  else if h : l.triples ≤ a ∧ a < l.triples+3*l.rows then
    let i : Fin l.rows := ⟨(a-l.triples)/3,by omega⟩
    let j : Fin 3 := ⟨(a-l.triples)%3,Nat.mod_lt _ (by decide)⟩
    fields ((dest tag).symm i) j
  else if h : l.cursors ≤ a ∧ a < l.cursors+l.cells then
    let c : Fin l.cells := ⟨a-l.cursors,by omega⟩
    start tag c.val + count tag c
  else before a

/-- The native bucket result fixes the complete word memory used by all
subsequent stages, including when either of the output tables is empty. -/
theorem Result.memory {before after : NatState} (result : Result l tag fields before after) :
    after.mem = l.wordImage tag fields before.mem := by
  funext a
  unfold Layout.wordImage
  split
  · rename_i h
    let c : Fin l.cells := ⟨(a-l.pairs)/2,by omega⟩
    split
    · rename_i even
      have pos : l.pairs+2*c.val=a := by dsimp [c]; omega
      exact (congrArg after.mem pos.symm).trans (result.starts c)
    · rename_i odd
      have pos : l.pairs+2*c.val+1=a := by dsimp [c]; omega
      exact (congrArg after.mem pos.symm).trans (result.counts c)
  · rename_i noHeader
    split
    · rename_i h
      let i : Fin l.rows := ⟨(a-l.triples)/3,by omega⟩
      let j : Fin 3 := ⟨(a-l.triples)%3,Nat.mod_lt _ (by decide)⟩
      have word := result.fields ((dest tag).symm i) j
      rw [Equiv.apply_symm_apply] at word
      have pos : l.triples+3*i.val+j.val=a := by dsimp [i,j]; omega
      exact (congrArg after.mem pos.symm).trans word
    · rename_i noTriple
      split
      · rename_i h
        let c : Fin l.cells := ⟨a-l.cursors,by omega⟩
        have pos : l.cursors+c.val=a := by dsimp [c]; omega
        exact (congrArg after.mem pos.symm).trans (result.cursors c)
      · rename_i noCursor
        apply result.other
        all_goals unfold Outside; omega

end FragmentBucket

end BorderVNP
end Computability
end OAI
