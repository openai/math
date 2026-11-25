import OAI.Hierarchy.Models

namespace OAI
/-! # Appending an affine layer to an algebraic branching program -/

namespace Hierarchy.Rows

open scoped BigOperators

variable {F : Type*} {σ : Type} [CommSemiring F] [Fintype σ] {m a b : ℕ}

private theorem exists_layer_keep (g : Rows F σ m) (p : Fin a → Fin m)
    (l : Fin a → Fin b → Affine F σ) :
    ∃ (n : ℕ) (out : Rows F σ n) (prior : Fin m → Fin n) (s : Fin b → Fin n),
      (∀ v, out.values (prior v) = g.values v) ∧
      (∀ j, out.values (s j) = ∑ i, g.values (p i) * (l i j).polynomial) ∧
      n + out.edgeCount ≤ m + g.edgeCount + b * (a + 1) := by
  induction b with
  | zero =>
    exact ⟨m, g, id, Fin.elim0, fun _ => rfl, fun j => j.elim0, by simp⟩
  | succ b ih =>
    obtain ⟨n, out, prior, s, keep, vals, budget⟩ := ih (fun i j => l i j.castSucc)
    let edges : List (Fin n × Affine F σ) :=
      List.ofFn (fun i => (prior (p i), l i (Fin.last b)))
    refine ⟨n + 1, out.snoc edges, fun v => (prior v).castSucc,
      Fin.lastCases (Fin.last n) (fun j => (s j).castSucc), ?_, ?_, ?_⟩
    · intro v
      simpa only [values, Fin.lastCases_castSucc] using keep v
    · intro j
      refine Fin.lastCases ?_ (fun t => ?_) j
      · simp only [Fin.lastCases_last, values, edges, List.map_ofFn, List.sum_ofFn,
          Function.comp_apply, keep]
      · simpa only [Fin.lastCases_castSucc, values] using vals t
    · simp only [edgeCount, edges, List.length_ofFn, Nat.succ_mul]
      omega

/-- A layer with `a` incoming edges per output adds at most `b * (a + 1)` vertices and edges. -/
theorem exists_layer (g : Rows F σ m) (p : Fin a → Fin m) (l : Fin a → Fin b → Affine F σ) :
    ∃ (n : ℕ) (out : Rows F σ n) (s : Fin b → Fin n),
      (∀ j, out.values (s j) = ∑ i, g.values (p i) * (l i j).polynomial) ∧
      n + out.edgeCount ≤ m + g.edgeCount + b * (a + 1) := by
  obtain ⟨n, out, _, s, _, vals, budget⟩ := exists_layer_keep g p l
  exact ⟨n, out, s, vals, budget⟩

end Hierarchy.Rows

end OAI
