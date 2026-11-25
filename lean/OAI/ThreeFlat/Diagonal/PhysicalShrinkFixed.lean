import OAI.ThreeFlat.Diagonal.PhysicalShrinkWordSpace

namespace OAI
/-! # The fixed scalar constants for shrinking are independent of the repetition count -/
namespace ThreeFlat.Diagonal.PhysicalStage.Program
open scoped Classical
noncomputable section
variable {F : Type} [Field F]

def shrinkWordConstants : {s : ℕ} → Program F s → List ℕ
  | _,.done _=>[]
  | _,.shrink s t T _ p=>shrinkFixedWords T s (2^t)::p.shrinkWordConstants
  | _,.refresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p=>p.shrinkWordConstants

theorem shrinkWordConstants_cast {s t : ℕ} (eqv : s=t) (p : Program F s) :
    (eqv ▸ p : Program F t).shrinkWordConstants=p.shrinkWordConstants := by cases eqv;rfl


end
end ThreeFlat.Diagonal.PhysicalStage.Program

namespace ThreeFlat.Diagonal.PhysicalStage.Block
open scoped Classical
noncomputable section
variable {F : Type} [Field F] (B : Block F)

def shrinkConstants : ℕ → ℕ → List ℕ
  | 0,_=>[]
  | n+1,i=>shrinkFixedWords B.shrink (B.exponent i) (2^B.exponent (i+1))::shrinkConstants n (i+1)

def shrinkWordCap := (B.shrinkConstants B.levels 0).sum

theorem shrinkConstants_prefix (n i : ℕ) (P : Program F (B.exponent (i+n))) :
    (B.shrinkPrefix n i P).shrinkWordConstants=B.shrinkConstants n i++P.shrinkWordConstants := by
  induction n generalizing i with
  | zero=>rfl
  | succ n ih=>simp only [shrinkPrefix,shrinkConstants,Program.shrinkWordConstants,ih,
      Program.shrinkWordConstants_cast,List.cons_append]

theorem wordConstants_prefix (p : Program F (B.exponent 0)) :
    (B.prefix p).shrinkWordConstants=B.shrinkConstants B.levels 0++p.shrinkWordConstants := by
  simp only [Block.prefix,shrinkConstants_prefix,Program.shrinkWordConstants_cast,Program.shrinkWordConstants]

theorem shrink_word_constant (n : ℕ) {a : ℕ} (occurs : a∈(B.repeat n).shrinkWordConstants) :
    a≤B.shrinkWordCap := by
  have selected : a∈B.shrinkConstants B.levels 0 := by
    induction n with
    | zero=>simp [Block.repeat,Program.shrinkWordConstants] at occurs
    | succ n ih=>
      rw [Block.repeat,B.wordConstants_prefix,List.mem_append] at occurs
      exact occurs.elim id ih
  exact List.le_sum_of_mem selected


end
end ThreeFlat.Diagonal.PhysicalStage.Block

end OAI
