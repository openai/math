import OAI.Computability.NearSquareRoot.PhysicalWalshCompileNode
import OAI.Computability.NearSquareRoot.PhysicalWalshAgendaOps

/-! # Finite execution budgets for every admitted recursive Walsh piece -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompile.Node

open IntegerMultiplication Code Space PhysicalWalsh PhysicalWalshNode KernelPass

/-- At a fixed depth only finitely many descended shapes can be requested.
The largest of their budgets covers every call made by the template. -/
private def treeBudget (A W calls C : ℕ) (scan : Shape → ℕ) : ℕ → Shape → ℕ
  | 0, s => C*(scan s+1)
  | n+1, s => C*(scan s+1)+(calls+1)*Finset.univ.sup (fun i : Fin A =>
      treeBudget A W calls C scan n (descend A W i s))

private theorem finiteRecurrence {a W : ℕ} (hw : 0 < W) (p : Plan (a+1) W W)
    (scan arena : Shape → ℕ) (cost : ∀ s, arena s ≤ scan s) (C : ℕ) :
    ∃ f : Shape → ℕ, Nonempty ((spec hw p scan arena cost).Recurrence p.calls C f f) := by
  let B := treeBudget (a+1) W p.calls C scan
  let f (s : Shape) := B s.level s
  let next (s : Shape) := Finset.univ.sup (fun i : Fin (a+1) => B (s.level-1) (descend (a+1) W i s))
  have child {u v : Shape} (h : childShape (a+1) W u v) : f v ≤ next u := by
    obtain ⟨_,_,i,rfl⟩ := h
    exact Finset.le_sup (f:=fun j : Fin (a+1) => B (u.level-1) (descend (a+1) W j u)) (Finset.mem_univ i)
  have base (u : Shape) (h : u.level = 0) : f u = C*(scan u+1) := by
    simp only [f,h,B,treeBudget]
  have step (u : Shape) (h : 0 < u.level) : f u = C*(scan u+1)+(p.calls+1)*next u := by
    unfold f
    rw [show u.level = (u.level-1)+1 by omega]
    rfl
  refine ⟨f,⟨next,next,child,child,fun u h => (base u h).ge,?_,?_,?_⟩⟩
  · intro u h
    rw [base u h]
    exact Nat.mul_le_mul_left _ (Nat.succ_le_succ (cost u))
  · intro u h
    rw [step u h]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ _)) _
  · intro u h
    rw [step u h]
    exact Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.succ_le_succ (cost u)))
      (Nat.le_mul_of_pos_left _ (Nat.succ_pos p.calls))

/-- A traced recursive command, prefixed by the actual tag scan, has a finite
execution on every admitted input without any growth assumption on the meter. -/
theorem total_of_trace {a W : ℕ} (hw : 0 < W) (p : Plan (a+1) W W)
    (scan arena : Shape → ℕ) (cost : ∀ s, arena s ≤ scan s) (cmd : Cmd)
    (run : AllTrace hw p scan arena cost cmd) :
    ∃ t s, EffectiveBoundedTask.Runs (entry.join cmd) t s (rawInput hw p) (rawOutput hw p) := by
  let vm := spec hw p scan arena cost
  let u (i : Admitted hw p) := i.val.shape
  obtain ⟨C,exec⟩ := run
  obtain ⟨f,⟨cert⟩⟩ := finiteRecurrence hw p scan arena cost C
  have node : EffectiveBoundedTask.Runs cmd (f ∘ u) (f ∘ u)
      (fun i => vm.query i.val) (rawOutput hw p) := by
    refine ⟨1,fun i env park b hb => ?_⟩
    have h := exec f f cert i.val env park b hb
    exact h.mono (by simp [u,spec]) (by simp [u,spec]) (by simp [u,spec])
  have start : EffectiveBoundedTask.Runs entry (fun i => allowance (a+1) 1 (u i))
      (fun i => allowance (a+1) 1 (u i)) (rawInput hw p) (fun i => vm.query i.val) :=
    entry_shape (fun _ => a+1) u (fun i => i.val.row)
  exact ⟨_,_,AgendaOps.compose start node⟩

end PhysicalWalshCompile.Node

end NearSquareRoot
end Computability
end OAI
