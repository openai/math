import OAI.ThreeFlat.RAM.Weighted

namespace OAI
/-! # Executing finite deterministic prefixes of a native program -/

namespace ThreeFlat.RAM

open Computability.VPVNP.BurstRAM

variable {w : ℕ} {C F : Type*}

/-- Advance by exactly the requested number of native instructions. A choice,
return, or rejection within that prefix does not give a continuation state. -/
def advance (P : Program w C) : ℕ → C → Memory w → Option (C × Memory w)
  | 0, c, m => some (c, m)
  | t+1, c, m =>
    match P.step c with
    | .localStep next => advance P t next m
    | .read a next => advance P t (next (m a.val)) m
    | .write a v next => advance P t next (writeMemory m a v)
    | _ => none

theorem advance_add (P : Program w C) (l r : ℕ) (c : C) (m : Memory w) :
    advance P (l+r) c m =
      (advance P l c m).bind (fun s => advance P r s.1 s.2) := by
  induction l generalizing c m with
  | zero => simp [advance]
  | succ l ih =>
    rw [Nat.succ_add, advance, advance]
    cases P.step c <;> simp [ih]

theorem advance_trans {P : Program w C} {l r : ℕ} {c d e : C} {m n o : Memory w}
    (left : advance P l c m = some (d,n)) (right : advance P r d n = some (e,o)) :
    advance P (l+r) c m = some (e,o) := by
  rw [advance_add, left]
  exact right

theorem mass_of_advance [Semiring F] (code : FieldCode F w) (P : Program w C)
    {t : ℕ} {c c' : C} {m m' : Memory w} (ok : advance P t c m = some (c',m'))
    (fuel : ℕ) : mass code P (fuel+t) c m = mass code P fuel c' m' := by
  induction t generalizing c m with
  | zero =>
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj ok)
    rfl
  | succ t ih =>
    rw [Nat.add_succ, mass]
    unfold advance at ok
    cases e : P.step c <;> rw [e] at ok <;> first | exact ih ok | contradiction

end ThreeFlat.RAM

end OAI
