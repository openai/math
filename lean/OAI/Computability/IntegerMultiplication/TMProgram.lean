import OAI.Computability.IntegerMultiplication.SM.Stack
import Mathlib.Logic.Function.Basic

namespace OAI
namespace Computability
namespace IntegerMultiplication

/-- Fixed structured program over stack instructions on (finitely many) named registers.
End of a program is return (a final program ends by halting). `tie a` creates a local
recursion in the *control*: within a, `again 0` means re-enter a. Nested blocks can
refer to an outer block with `again 1`, etc. Unbound references have no successful
execution. The tape implementation will use a stack for return addresses. -/
inductive Prog (A : Type) : Type
  | pass
  | push (i : ℕ) (x : A)
  | pop (i : ℕ)
  | look (i : ℕ) (c : Option A → Prog A)
  | join (c d : Prog A)
  | tie (body : Prog A)
  | again (up : ℕ)

/-- Data register assignment; register numbers will not be computed by the machine. -/
abbrev Reg (A : Type) := ℕ → List A
abbrev Scope (A : Type) := List (Prog A)

namespace Prog
variable {A : Type}

/-- Costs include entry at every program node and the control branch to the second
subprogram of a sequence after the first returns (on tape this pops a return address).
Entry into recursion does not copy data. -/
inductive Run : Scope A → Prog A → Reg A → ℕ → Reg A → Prop
  | pass {Γ r} : Run Γ .pass r 1 r
  | push {Γ i x r} : Run Γ (.push i x) r 1 (Function.update r i (x::r i))
  | pop {Γ i r} : Run Γ (.pop i) r 1 (Function.update r i (r i).tail)
  | look {Γ i c r n r'} : Run Γ (c (r i).head?) r n r' → Run Γ (.look i c) r (1+n) r'
  | join {Γ c d r n₁ s n₂ t} :
    Run Γ c r n₁ s → Run Γ d s n₂ t → Run Γ (.join c d) r (1+n₁+1+n₂) t
  | tie {Γ c r n r'} :
    Run (c::Γ) c r n r' → Run Γ (.tie c) r (1+n) r'
  | again {Γ i c r n r'} :
    Γ[i]? = some c → Run (Γ.drop i) c r n r' → Run Γ (.again i) r (1+n) r'

/-- Injective substitution of registers in a program. -/
def rename (j : ℕ → ℕ) (p : Prog A) : Prog A :=
  match p with
  | .pass => .pass
  | .push i x => .push (j i) x
  | .pop i => .pop (j i)
  | .look i c => .look (j i) (fun v => rename j (c v))
  | .join c d => .join (rename j c) (rename j d)
  | .tie c => .tie (rename j c)
  | .again i => .again i

/-- Replace all renamed registers in w via the old register assignment r. This def
is for reasoning; it's not a machine operation. -/
noncomputable def paint (j : ℕ → ℕ) (r w : Reg A) : Reg A :=
  open Classical in fun i => if h : ∃ l, i=j l then r (choose h) else w i

variable {j : ℕ → ℕ} (hj : Function.Injective j)

include hj in
theorem paint_at (r w : Reg A) (i : ℕ) : paint j r w (j i) = r i := by
  unfold paint
  split
  · next h => exact congrArg r (hj (Classical.choose_spec h)).symm
  · simp_all

theorem paint_else (r w : Reg A) (i : ℕ) (h : ∀ l, i ≠ j l) :
    paint j r w i = w i := by
  unfold paint
  split
  · next p => obtain ⟨l,e⟩ := p; exact ((h l) e).elim
  · rfl

include hj
private theorem paint_update (r w : Reg A) (i) (x : List A) :
    paint j (Function.update r i x) w = Function.update (paint j r w) (j i) x := by
  funext l
  by_cases hl : ∃ n, l=j n
  · obtain ⟨n,rfl⟩ := hl
    by_cases heq : n=i
    · subst n; rw [paint_at hj, Function.update_self, Function.update_self]
    · rw [paint_at hj, Function.update_of_ne heq, Function.update_of_ne (hj.ne heq), paint_at hj]
  · have h : ∀ n, l ≠ j n := by simpa using hl
    rw [paint_else _ w _ h, Function.update_of_ne (h i), paint_else _ w _ h]

theorem Run.rename {Γ : Scope A} {c r n s} (h : Run Γ c r n s) (w : Reg A) :
    Run (Γ.map (Prog.rename j)) (Prog.rename j c) (paint j r w) n (paint j s w) := by
  induction h with
  | pass => exact .pass
  | @push G i x b =>
    rw [paint_update hj, Prog.rename]
    rw [← paint_at hj b w i]
    exact .push
  | @pop G i b =>
    rw [paint_update hj, Prog.rename, ← paint_at hj b w i]
    exact .pop
  | @look G i c b n' b' h ih =>
    dsimp [Prog.rename]
    rw [← paint_at hj b w i] at ih
    exact .look ih
  | join _ _ ih jh => exact .join ih jh
  | tie _ ih =>
    exact .tie ih
  | @again G i c b n' b' e _ ih =>
    rw [List.map_drop] at ih
    exact .again (by rw [List.getElem?_map, e]; rfl) ih

end Prog

end IntegerMultiplication
end Computability
end OAI
