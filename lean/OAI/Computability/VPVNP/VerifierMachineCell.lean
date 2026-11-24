import OAI.Computability.BinPacking.CookLevin.ConfigIndex
import OAI.Computability.VPVNP.VerifierMachineSimulation

/-!
# One tape cell in the Boolean coefficient verifier

For a fixed candidate move, the destination reads a blank at the boundary, the written
symbol at the old head, and the old symbol at every other source. A disjunction over the
three moves selects this candidate, and a multiplexer preserves the tape on halted branches.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace UniversalMachine

open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit

variable {ι : Type*} {r : ℕ}

/-- The symbol bit at a destination for a fixed candidate move. -/
private def movedCell (old : WindowCell r → Symbol → Expr ι) (write : Symbol → Expr ι)
    (d : Fin 3) (i : WindowCell r) (s : Symbol) : Expr ι :=
  match shiftSource d i with
  | none => .const (decide ((0 : Symbol) = s))
  | some j => if j = windowCenter r then write s else old j s

/-- The new one-hot bit for symbol `s` at tape cell `i`. -/
def cellNext (old : WindowCell r → Symbol → Expr ι) (present : Expr ι)
    (write move : Fin 3 → Expr ι) (i : WindowCell r) (s : Symbol) : Expr ι :=
  Expr.mux present
    (Expr.disjoin (List.ofFn fun d => Expr.and (move d) (movedCell old write d i s)))
    (old i s)

theorem cellNext_eval_none (old : WindowCell r → Symbol → Expr ι) (present : Expr ι)
    (write move : Fin 3 → Expr ι) (i : WindowCell r) (s : Symbol) (x : ι → Bool)
    (hp : present.eval x = false) :
    (cellNext old present write move i s).eval x = (old i s).eval x := by
  simp [cellNext, hp]

private theorem movedCell_eval (old : WindowCell r → Symbol → Expr ι)
    (write : Symbol → Expr ι) (d : Fin 3) (i : WindowCell r) (s : Symbol)
    (x : ι → Bool) (tape : WindowTape r) (w : Symbol)
    (ho : ∀ j a, (old j a).eval x = decide (tape j = a))
    (hw : ∀ a, (write a).eval x = decide (w = a)) :
    (movedCell old write d i s).eval x = decide (windowUpdate tape w d i = s) := by
  cases h : shiftSource d i with
  | none => simp [movedCell, windowUpdate, h, Expr.eval]
  | some j =>
    by_cases hc : j = windowCenter r <;> simp [movedCell, windowUpdate, h, hc, ho, hw]

theorem cellNext_eval_some (old : WindowCell r → Symbol → Expr ι) (present : Expr ι)
    (write move : Fin 3 → Expr ι) (i : WindowCell r) (s : Symbol) (x : ι → Bool)
    (tape : WindowTape r) (w d : Fin 3)
    (hp : present.eval x = true)
    (ho : ∀ j a, (old j a).eval x = decide (tape j = a))
    (hw : ∀ a, (write a).eval x = decide (w = a))
    (hm : ∀ k, (move k).eval x = decide (d = k)) :
    (cellNext old present write move i s).eval x = decide (windowUpdate tape w d i = s) := by
  simp only [cellNext, Expr.eval_mux, hp, ite_true]
  apply Bool.eq_iff_iff.mpr
  simp only [Expr.eval_disjoin_true, List.mem_ofFn, exists_exists_eq_and, Expr.eval,
    Bool.and_eq_true, hm, decide_eq_true_eq, movedCell_eval old write _ i s x tape w ho hw]
  simp

theorem cellNext_size_le (old : WindowCell r → Symbol → Expr ι) (present : Expr ι)
    (write move : Fin 3 → Expr ι) (i : WindowCell r) (s : Symbol) (C : ℕ)
    (ho : ∀ j a, (old j a).size ≤ C) (hp : present.size ≤ C)
    (hw : ∀ a, (write a).size ≤ C) (hm : ∀ k, (move k).size ≤ C) :
    (cellNext old present write move i s).size ≤ 12 * (C + 1) := by
  have hpos := present.size_pos
  have hcell (d : Fin 3) : (movedCell old write d i s).size ≤ C := by
    unfold movedCell
    split
    · simp only [Expr.size]
      omega
    · split <;> first | exact hw s | exact ho _ s
  have hall := Expr.size_disjoin_le
    (List.ofFn fun d => Expr.and (move d) (movedCell old write d i s)) (2 * C + 1) (by
      intro e he
      obtain ⟨d, rfl⟩ := List.mem_ofFn.mp he
      simp only [Expr.size]
      have := hcell d
      have := hm d
      omega)
  simp only [List.length_ofFn] at hall
  simp only [cellNext, Expr.mux, Expr.size]
  have := ho i s
  omega

end UniversalMachine

end VPVNP
end Computability
end OAI
