import OAI.Hierarchy.Models
import Mathlib.Algebra.BigOperators.Ring.List

namespace OAI
/-! # Copying a branching program from an existing vertex

The source of the copied program is identified with a chosen vertex. Each subsequent
row keeps all of its incoming edges and points them to the corresponding copied vertices.
-/

namespace Hierarchy
noncomputable section

variable {F : Type*} {σ : Type} [CommSemiring F] [Fintype σ]

private theorem copyRows {n k : ℕ} (g : Rows F σ n) (v : Fin n) (h : Rows F σ k) :
    ∃ (m : ℕ) (le : n ≤ m) (out : Rows F σ m) (ref : Fin k → Fin m),
      (∀ i : Fin n, out.values (i.castLE le) = g.values i) ∧
      (∀ i : Fin k, out.values (ref i) = g.values v * h.values i) ∧
      m + out.edgeCount ≤ n + g.edgeCount + (k + h.edgeCount) := by
  induction h with
  | source =>
    refine ⟨n, le_rfl, g, fun _ => v, fun _ => rfl, ?_, ?_⟩
    · intro i
      simp [Rows.values]
    · simp [Rows.edgeCount]
  | @snoc k prev edges ih =>
    obtain ⟨m, le, out, ref, keep, copied, cost⟩ := ih
    let edges' : List (Fin m × Affine F σ) := edges.map (fun e => (ref e.1, e.2))
    let ref' : Fin (k + 1) → Fin (m + 1) :=
      Fin.lastCases (Fin.last m) (fun i => (ref i).castSucc)
    refine ⟨m + 1, le.trans (Nat.le_succ _), out.snoc edges', ref', ?_, ?_, ?_⟩
    · intro i
      change (out.snoc edges').values (i.castLE le).castSucc = _
      simpa only [Rows.values, Fin.lastCases_castSucc] using keep i
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [ref', Fin.lastCases_last, Rows.values, edges', List.map_map,
          Function.comp_def, copied, mul_assoc, List.sum_map_mul_left]
      · simpa only [ref', Fin.lastCases_castSucc, Rows.values] using copied j
    · simp only [Rows.edgeCount, edges', List.length_map]
      omega

/-- Append a copy of an ABP to a graph, identifying the source of the copy with
`v`. Existing vertex values persist, and the copy computes its original polynomial
times the value at `v`. -/
theorem ABP.copyFrom {n : ℕ} (h : ABP F σ) (g : Rows F σ n) (v : Fin n) :
    ∃ (m : ℕ) (le : n ≤ m) (out : Rows F σ m) (s : Fin m),
      (∀ i : Fin n, out.values (i.castLE le) = g.values i) ∧
      out.values s = g.values v * h.polynomial ∧
      m + out.edgeCount ≤ n + g.edgeCount + h.size := by
  obtain ⟨m, le, out, ref, keep, copied, cost⟩ := copyRows g v h.rows
  exact ⟨m, le, out, ref h.sink, keep, copied h.sink, cost⟩

end
end Hierarchy

end OAI
