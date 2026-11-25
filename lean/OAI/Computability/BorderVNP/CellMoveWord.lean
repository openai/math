import OAI.Computability.BorderVNP.CellFragmentWords

/-! # Order-preserving transfer of a generator word -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellMacro.Generator.Fragment

open VPVNP.RAMTape RationalHitting.StackLanguage

variable {K : Type} [DecidableEq K]

/-- Updating one public register does not affect the private bank. -/
theorem update_left {J : Type} [DecidableEq J] (s : Stacks K) (z : Stacks J) (k : K) (w : List Bool) :
    Function.update (Sum.elim s z) (.inl k) w = Sum.elim (Function.update s k w) z := by
  funext i
  cases i with
  | inl i => by_cases hi : i = k <;> simp [hi]
  | inr i => simp

/-- Updating one private register does not affect the public bank. -/
theorem update_right {J : Type} [DecidableEq J] (s : Stacks K) (z : Stacks J) (j : J) (w : List Bool) :
    Function.update (Sum.elim s z) (.inr j) w = Sum.elim s (Function.update z j w) := by
  funext i
  cases i with
  | inl i => simp
  | inr i => by_cases hi : i = j <;> simp [hi]

/-- Move a word to an empty destination, using two reversals through a private register. -/
def moveWord (src dst : K) : Fragment K where
  Scratch := Unit
  body := Structured.lower (move (.inl src) (.inl dst) (.inr ()))

/-- Both the source and the temporary register are empty on return. -/
theorem moveWord_run {src dst : K} (hd : src ≠ dst) (s : Stacks K) (hdst : s dst = []) :
    ∃ t ≤ 2*(4*(s src).length+3), (moveWord src dst).Runs t s
      (Function.update (Function.update s src []) dst (s src)) := by
  let r := moveWord src dst
  obtain ⟨t, ht, hr⟩ := Structured.run (eval_move (a := Sum.inl src) (b := Sum.inl dst)
    (tmp := Sum.inr ()) (by simpa) (by simp) (by simp) (r.bank s) hdst rfl)
  refine ⟨t, ht, ?_⟩
  erw [update_left, update_left] at hr
  exact hr

end CellMacro.Generator.Fragment

end BorderVNP
end Computability
end OAI
