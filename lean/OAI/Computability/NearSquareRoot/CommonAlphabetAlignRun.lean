import OAI.Computability.NearSquareRoot.CommonAlphabetAlign

/-! # Exact logical checkpoints of the folded-distance machine -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CommonAlphabet.Align
open IntegerMultiplication TM
variable {A Q I : Type} [DecidableEq A] [DecidableEq I]

def Known (out : I) (x : Config A Q I) (neg : Bool) :=
  (x.tape out).pos ≠ 0 → neg = decide ((x.tape out).pos < 0)

theorem sim (out : I) (blank marker : A) (hne : blank ≠ marker) (entry : Q) (m : Rule A Q I)
    {x y : Config A Q I} {n : ℕ} (run : Trace (advance m) x n y) (neg : Bool) (known : Known out x neg) :
    ∃ neg', Known out y neg' ∧ Trace (advance (rule out blank marker entry m))
      (running out blank marker neg x) n (running out blank marker neg' y) := by
  induction run generalizing neg with
  | nil => exact ⟨neg,known,.nil _⟩
  | cons first _ ih =>
    obtain ⟨mid,hm,hs⟩ := tick out blank marker hne entry m first neg known
    obtain ⟨last,hl,tail⟩ := ih mid hm
    exact ⟨last,hl,.cons hs tail⟩

theorem checkpoint (out : I) (blank marker : A) (hne : blank ≠ marker) (m : Rule A Q I)
    {x y : Config A Q I} {n : ℕ} (zero : (x.tape out).pos=0) (run : Trace (advance m) x n y) :
    ∃ neg, Known out y neg ∧ Trace (advance (rule out blank marker x.pc m)) (initial x blank)
      (n+1) (running out blank marker neg y) := by
  obtain ⟨b,hb,actual⟩ := sim out blank marker hne x.pc m run false (by simp [Known,zero])
  exact ⟨b,hb,by simpa only [Nat.add_comm 1] using Trace.cons (start out blank marker m x zero) actual⟩

end CommonAlphabet.Align

end NearSquareRoot
end Computability
end OAI
