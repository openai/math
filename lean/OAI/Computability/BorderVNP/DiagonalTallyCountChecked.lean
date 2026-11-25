import OAI.Computability.BorderVNP.DiagonalTallyOperandRead

/-! # Reindexing an accepted private count into the absolute external report bank -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyOperandArray

open VPVNP.TapeWord CellSparse DiagonalTallyCellReports

private theorem word_eq_value (bank : ℕ → Bool) (xs : List ℕ) :
    CellSparse.word bank xs=value (xs.map bank) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => cases e : bank a <;> simp [CellSparse.word,value,e,ih]

/-- The native count operand of a passing cell counts the corresponding observed
ID at its absolute external addresses. The cell check itself uses private-bank indices. -/
theorem Frame.count_pair_checked (f : Frame) (g : Fin f.gadgets) (base : ℕ) (bank : ℕ → Bool)
    (D : Directory) (fields : D.reportedCounts=countFields base f.gadgets f.width)
    (obs : List (Bool × Option ℕ)) (valid : countsValid bank D.reportedCounts obs) :
    (f.countRow g (fun j => bank (base+g.val*f.width+j.val))).pair =
      (f.parameters+g.val,(obs.filterMap Prod.snd).count g.val) := by
  rw [fields] at valid
  let a : Fin (countFields base f.gadgets f.width).length := ⟨g.val,by simp⟩
  have hg := valid.2 a
  simp [a,word_eq_value,countFields,List.map_ofFn,Function.comp_def] at hg
  rw [f.count_pair,hg]

end DiagonalTallyOperandArray

end BorderVNP
end Computability
end OAI
