import OAI.Computability.VPVNP.BooleanTranscript

/-! # Local tests for a proposed shared Boolean computation

Every gate is checked on its two operand references (one in the case of negation)
and its proposed output. These tests force the entire gate assignment uniquely.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseBatch.BooleanRows

open VPVNP.BooleanTranscript

variable {σ : Type*}

/-- The instruction at position `i` can reference exactly the preceding positions. -/
def row : {n : ℕ} → Program σ n → (i : Fin n) → Gate σ i.val
  | _, .nil => fun i => i.elim0
  | _, .snoc p g => Fin.lastCases g (fun i => row p i)

/-- The values of the wires before `i`. -/
def before {n : ℕ} (v : Fin n → Bool) (i : Fin n) (j : Fin i.val) : Bool :=
  v ⟨j.val, j.isLt.trans i.isLt⟩

private theorem before_cast {n : ℕ} (v : Fin (n+1) → Bool) (i : Fin n) :
    before v i.castSucc = before (Fin.init v) i := rfl

private theorem before_last {n : ℕ} (v : Fin (n+1) → Bool) :
    before v (Fin.last n) = Fin.init v := rfl

/-- The product of the local constraints has a single satisfying gate transcript. -/
theorem rows_iff {n : ℕ} (p : Program σ n) (x : σ → Bool) (v : Fin n → Bool) :
    (∀ i, (row p i).eval x (before v i) = v i) ↔ v = p.run x := by
  induction p with
  | nil => simp [Subsingleton.elim v (Program.nil.run x)]
  | @snoc k p g ih =>
    constructor
    · intro h
      have prev : Fin.init v = p.run x := (ih (Fin.init v)).mp fun i => by
        simpa only [row, Fin.lastCases_castSucc, before_cast, Fin.init] using h i.castSucc
      have last : g.eval x (Fin.init v) = v (Fin.last k) := by
        simpa only [row, Fin.lastCases_last, before_last] using h (Fin.last k)
      funext i
      induction i using Fin.lastCases with
      | last => simpa [Program.run, ← prev] using last.symm
      | cast i => simpa only [Program.run, Fin.snoc_castSucc, Fin.init] using congrFun prev i
    · rintro rfl i
      induction i using Fin.lastCases with
      | last => simp [row, before_last, Program.run]
      | cast i =>
        simpa only [row, Fin.lastCases_castSucc, before_cast, Program.run, Fin.init_snoc,
          Fin.snoc_castSucc] using (ih (p.run x)).mpr rfl i

end ParseBatch.BooleanRows

end BorderVNP
end Computability
end OAI
