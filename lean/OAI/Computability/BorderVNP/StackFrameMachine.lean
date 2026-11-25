import OAI.Computability.BinPacking.CookLevin.BoundedExecution
import OAI.Computability.FiniteCompiler.Machines
import OAI.Computability.RationalHitting.Procedures

/-!
# Finite-control execution of a binary stack program

The support computed from the syntax contains every reachable continuation,
including those reached by returning to a loop. Restricting labels to this
support preserves each transition and hence the exact execution time.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace StackFrame

open Turing RationalHitting.StackLanguage RationalHitting.TMTime
open BinPackingGames.Foundations.Complexity.CookLevin
open FiniteAlgebraicEnvelopes.MachineRealization

variable {K : Type} [DecidableEq K] [Fintype K]

/-- Finite binary-stack machine obtained by restricting the control of a program
to its syntactic support. Input and output registers may coincide. -/
abbrev finiteMachine (p : Program K) (ki ko : K) : FinTM2 where
  K := K
  k₀ := ki
  k₁ := ko
  Γ := fun _ => Bool
  Λ := ↥(support p)
  main := ⟨none, (machine_supported p).1⟩
  σ := Option Bool
  initialState := none
  m := FiniteTM2.machine (machine p) (support p) (machine_supported p)

private theorem absorbing_of_exec {A : Type*} (step : A → Option A)
    (n : ℕ) {a b : A} (he : exec step n a = some b) :
    (BoundedExecution.absorbingNext step)^[n] a = b := by
  induction n generalizing a with
  | zero => exact Option.some.inj he
  | succ n ih =>
    cases hs : step a with
    | none => simp [exec, hs] at he
    | some c =>
      rw [Function.iterate_succ_apply, BoundedExecution.absorbingNext_of_some step hs]
      exact ih (by simpa [exec, hs] using he)

private theorem embed_sticky (p : Program K) (ki ko : K) :
    Function.Semiconj (FiniteTM2.embedCfg (support p))
      (BoundedExecution.stickyNext (finiteMachine p ki ko))
      (BoundedExecution.absorbingNext (TM2.step (machine p))) := by
  intro c
  let f := FiniteTM2.embedCfg (Γ := fun _ : K => Bool) (σ := Option Bool) (support p)
  let step := TM2.step (FiniteTM2.machine (machine p) (support p) (machine_supported p))
  have hs : (step c).map f = TM2.step (machine p) (f c) :=
    FiniteTM2.embed_step (machine p) (support p) (machine_supported p) c
  change f ((step c).getD c) = (TM2.step (machine p) (f c)).getD (f c)
  rw [← hs]
  cases step c <;> rfl

/-- After a successful stack evaluation, the finite machine halts with exactly
the prescribed output and stays there at any later clock horizon. There are two
additional steps, for entry and halt. -/
theorem run_of_eval (p : Program K) (ki ko : K) {w y : List Bool} {t T : ℕ}
    (h : Eval p (single ki w) (single ko y) t) (ht : t ≤ T) :
    BoundedExecution.run (finiteMachine p ki ko) w (T+2) = haltList (finiteMachine p ki ko) y := by
  let tm := finiteMachine p ki ko
  let embed := FiniteTM2.embedCfg (Γ := fun _ : K => Bool) (σ := Option Bool) (support p)
  have hi : embed (initList tm w) = ⟨some none, none, single ki w⟩ := by
    apply congrArg (TM2.Cfg.mk _ _)
    funext k
    by_cases hk : k = ki
    · subst k; simp [initList, tm, finiteMachine, single]
    · simp [initList, tm, finiteMachine, single, hk]
  have ho : embed (haltList tm y) = ⟨none, none, single ko y⟩ := by
    apply congrArg (TM2.Cfg.mk _ _)
    funext k
    by_cases hk : k = ko
    · subst k; simp [haltList, tm, finiteMachine, single]
    · simp [haltList, tm, finiteMachine, single, hk]
  apply FiniteTM2.embedCfg_injective (support p)
  let raw := BoundedExecution.absorbingNext (TM2.step (machine p))
  change embed ((BoundedExecution.stickyNext tm)^[T+2] (initList tm w)) = embed (haltList tm y)
  calc
    _ = raw^[T+2] (embed (initList tm w)) :=
      (embed_sticky p ki ko).iterate_right (T+2) (initList tm w)
    _ = raw^[T+2] ⟨some none, none, single ki w⟩ := congrArg raw^[T+2] hi
    _ = ⟨none, none, single ko y⟩ := by
      have hs : raw^[t+2] ⟨some none, none, single ki w⟩ = ⟨none, none, single ko y⟩ :=
        absorbing_of_exec _ _ (complete_run h)
      rw [show T+2 = (T-t)+(t+2) by omega, Function.iterate_add_apply, hs]
      exact Function.iterate_fixed (BoundedExecution.absorbingNext_of_none _ rfl) _
    _ = embed (haltList tm y) := ho.symm

end StackFrame

end BorderVNP
end Computability
end OAI
