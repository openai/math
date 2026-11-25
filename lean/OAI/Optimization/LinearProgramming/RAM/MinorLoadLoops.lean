import OAI.Optimization.LinearProgramming.RAM.Loops
import Mathlib.Algebra.BigOperators.Fin

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Block
namespace Eval

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Costs of inner RAM passes may depend on the loop index. Both guard evaluations and
back edges are retained in the sum. -/
theorem loop_varying_exact {safe : Memory K → Prop} {c : Cond} {body : Block}
    (n : ℕ) (cost : Fin n → ℕ) (I : ℕ → Memory K → Prop) (m : Memory K) (hstart : I 0 m)
    (hbody : ∀ j : Fin n, ∀ s, I j.val s → c.test s = true ∧
      ∃ t, Eval safe body s (cost j) t ∧ I (j.val+1) t)
    (hstop : ∀ s, I n s → c.test s = false ∧ safe s) :
    ∃ t, Eval safe (.loop c body) m ((∑ j, (cost j+2))+1) t ∧ I n t := by
  induction n generalizing I m with
  | zero =>
    obtain ⟨hf,hs⟩ := hstop m hstart
    exact ⟨m, by simpa using Eval.loopFalse (body := body) hf hs, hstart⟩
  | succ n ih =>
    obtain ⟨hg, t, hfirst, ht⟩ := hbody 0 m hstart
    obtain ⟨u, hrest, hu⟩ := ih (fun j => cost j.succ) (fun j => I (j+1)) t ht
      (fun j => hbody j.succ) hstop
    refine ⟨u, ?_, hu⟩
    rw [Fin.sum_univ_succ]
    convert Eval.loopTrue hg hfirst hrest using 1; omega

end Eval
end Block
end RAM
end LinearProgramming
end Optimization
end OAI
