import OAI.Computability.VPVNP.EvaluatorMatrixStep

/-! # Composition of time-bounded evaluator routines

A routine realizes a transition when any continuation with a reserved amount
of fuel returns the prescribed count on the resulting states. This permits
different branches to use different numbers of instructions.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace EvaluatorRoutine

open RAMTape

variable {K Q R S T U I : Type*} [DecidableEq K]

/-- The caller reserves `extra` instructions after the routine's per-path
bound `B`. Its count on each encoded output determines the whole transition. -/
def Realizes (r : Routine K Q) (pre : S → Stacks K) (post : T → Stacks K)
    (B : ℕ) (effect : (T → ℕ) → S → ℕ) : Prop :=
  ∀ (extra fuel : ℕ), extra + B ≤ fuel → ∀ (x : S) (f : T → ℕ) (c : ℕ → Stacks K → ℕ),
    (∀ y k, extra ≤ k → c k (post y) = f y) → r.count c fuel (pre x) = effect f x

variable {r : Routine K Q} {r' : Routine K R} {pre : S → Stacks K} {mid : T → Stacks K}
    {post : U → Stacks K} {B B' : ℕ} {e : (T → ℕ) → S → ℕ} {e' : (U → ℕ) → T → ℕ}

theorem Realizes.mono (h : Realizes r pre mid B e) (hB : B ≤ B') :
    Realizes r pre mid B' e :=
  fun extra fuel hf => h extra fuel ((Nat.add_le_add_left hB _).trans hf)

theorem Realizes.followedBy (ha : Realizes r pre mid B e) (hb : Realizes r' mid post B' e') :
    Realizes (r.followedBy r') pre post (B+B') (fun f x => e (e' f) x) := by
  intro extra fuel hf x f c hc
  rw [Routine.count_followedBy]
  apply ha (extra+B') fuel (by omega)
  intro y left hl
  exact hb extra left hl y f c hc

/-- A deterministic prefix spends its actual cost and preserves one branch. -/
theorem Realizes.of_runs {g : S → T} (h : ∀ x, ∃ d ≤ B, r.Runs d (pre x) (mid (g x))) :
    Realizes r pre mid B (fun f x => f (g x)) := by
  intro extra fuel hf x f c hc
  obtain ⟨d, hd, hr⟩ := h x
  have he := hr.count_eq c (fuel-d)
  rw [Nat.sub_add_cancel (by omega)] at he
  exact he.trans (hc _ _ (by omega))

/-- Bounded delays on a finite family of outcomes establish a transition
whose multiplicity is their ordinary sum. -/
theorem Realizes.of_delay [Fintype I] {next : S → I → T}
    (h : ∀ x fuel, B ≤ fuel → ∃ d : I → ℕ, (∀ i, d i ≤ B) ∧ ∀ c,
      r.count c fuel (pre x) = ∑ i, c (fuel-d i) (mid (next x i))) :
    Realizes r pre mid B (fun f x => ∑ i, f (next x i)) := by
  intro extra fuel hf x f c hc
  obtain ⟨d, hd, he⟩ := h x fuel (by omega)
  rw [he]
  exact Finset.sum_congr rfl fun i _ => hc _ _ (by have := hd i; omega)

end EvaluatorRoutine

end VPVNP
end Computability
end OAI
