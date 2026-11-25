import OAI.ThreeFlat.Diagonal.ProgramDirectoryData

namespace OAI
/-! # Directory length of a finite number of complete physical shrink–refresh blocks -/

namespace ThreeFlat.Diagonal.PhysicalStage.Block

variable {F : Type} [Field F] (B : Block F)

private theorem length_cast {s t : ℕ} (e : s=t) (p : Program F s) :
    (e ▸ p : Program F t).length=p.length := by cases e;rfl

private theorem length_shrinkPrefix (n i : ℕ) (p : Program F (B.exponent (i+n))) :
    (B.shrinkPrefix n i p).length=n+p.length := by
  induction n generalizing i with
  | zero => simp [shrinkPrefix]
  | succ n ih =>
    simp only [shrinkPrefix,Program.length,ih,length_cast]
    omega

theorem length_repeat (n : ℕ) : (B.repeat n).length=(B.levels+1)*n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Block.repeat,Block.prefix,length_shrinkPrefix,length_cast,Program.length,ih,Nat.mul_succ]
    omega

end ThreeFlat.Diagonal.PhysicalStage.Block

end OAI
