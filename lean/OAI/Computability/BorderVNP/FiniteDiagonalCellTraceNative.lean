import OAI.Computability.BorderVNP.CellStackTape
import OAI.Computability.BorderVNP.FinitePrivateReturnTape

/-! # Individual field returns of the cell's private stack-to-tape compiler

Each continuing stack instruction takes two native steps. The middle step
never branches. Hence each particular consumed binary tape, including an empty
tape and a successful scalar zero, has exactly its original stack return.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal.CellTrace

open VPVNP.RAMTape TeamPrivateTape CellMacro.StackTape
open private stay seek write pop head stay_eq push_eq pop_eq head_eq from OAI.Computability.BorderVNP.CellStackTape

variable {K Q : Type} {m : ℕ} [DecidableEq K] {F : Type*}

/-- Lift a stack terminal output to the native finite-state machine. Successful
terminal instructions occur only in a ready state. -/
def terminalOutput (weight : Q → F) : FieldSelect.Return (Control Q m) (Option Bool) F m
  | .ready q, _, _ => weight q
  | .idle q, _, _ | .write _ _ q, _, _ => weight q

/-- At twice the stack clock, each individual consumed choice tape gives exactly
the indicated field output in the installed multitape instruction table. -/
theorem nativeReturn_iff (e : K ≃ Fin m) (C : StackCode K Q) (neg : Q → Bool) (weight : Q → F)
    (fuel : ℕ) (q : Q) (t : Fin m → SymbolTape (Option Bool)) (bs : List Bool) (z : F) :
    FieldSelect.nativeReturn (table e C neg) none (terminalOutput weight) (2*fuel) (.ready q) t bs = some z ↔
      (bs,z) ∈ FieldReplay.leaves C weight fuel q (values e t) := by
  classical
  have idle (q : Control Q m) (t : Fin m → SymbolTape (Option Bool)) :
      (⟨q,fun i => (t i).head,fun _ => none⟩ : TapeCommand _ _ m).apply none t = t := stay_eq t q
  induction fuel generalizing q t bs with
  | zero => simp [FieldSelect.nativeReturn,FieldReplay.leaves]
  | succ fuel ih =>
    rw [Nat.mul_succ]
    cases h : C q with
    | halt ok =>
      cases ok <;> cases bs <;> simp [FieldSelect.nativeReturn,FieldReplay.leaves,table,h,terminalOutput,eq_comm]
    | goto r =>
      simp only [FieldSelect.nativeReturn,table,h,FieldReplay.leaves,stay]
      exact ih r t bs
    | choose l r =>
      rw [FieldReplay.mem_choose_iff C weight fuel q _ l r h]
      cases bs with
      | nil => simp [FieldSelect.nativeReturn,table,h]
      | cons b bs =>
        cases b
        · simpa [FieldSelect.nativeReturn,table,h,stay,idle] using ih l t bs
        · simpa [FieldSelect.nativeReturn,table,h,stay,idle] using ih r t bs
    | pop k f =>
      let u := (pop f (e k) (head t)).apply none t
      have hp := ih (f (head t (e k))) u bs
      simp only [FieldSelect.nativeReturn,table,h,FieldReplay.leaves]
      rw [← pop_eq e k f t,head_eq]
      exact hp
    | push k b r =>
      let u := (seek r (e k) b (head t)).apply none t
      have hp := ih r ((write r (e k) b (head u)).apply none u) bs
      simp only [FieldSelect.nativeReturn,table,h,FieldReplay.leaves]
      rw [← push_eq e k b r t]
      exact hp

end FiniteDiagonal.CellTrace

end BorderVNP
end Computability
end OAI
