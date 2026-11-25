import OAI.Hierarchy.ABPLayer
import OAI.Hierarchy.ChainProduct

namespace OAI
/-! # Affine branching programs for weighted path sums -/

namespace Hierarchy.ChainProduct

open scoped BigOperators
noncomputable section

variable {F : Type*} {σ : Type} [Field F] [Fintype σ] {q : ℕ}

private theorem prefix_rows (k : ℕ) (left : Fin q → Affine F σ)
    (middle : Fin k → Fin q → Fin q → Affine F σ) :
    ∃ (n : ℕ) (g : Rows F σ n) (state : Fin q → Fin n),
      (∀ j, g.values (state j) = prefixValue k (fun a => (left a).polynomial)
        (fun i a b => (middle i a b).polynomial) j) ∧
      n + g.edgeCount ≤ 1 + q * 2 + k * (q * (q + 1)) := by
  induction k with
  | zero =>
    obtain ⟨n,g,state,value,cost⟩ :=
      (Rows.source : Rows F σ 1).exists_layer (fun _ : Fin 1 => 0)
        (fun _ j => left j)
    refine ⟨n,g,state,fun j => ?_,?_⟩
    · simpa [Rows.values] using value j
    · simpa [Rows.edgeCount] using cost
  | succ k ih =>
    obtain ⟨n,g,state,prior,cost⟩ := ih (fun i => middle i.castSucc)
    obtain ⟨n',g',state',next,cost'⟩ := g.exists_layer state (middle (Fin.last k))
    refine ⟨n',g',state',fun j => ?_,?_⟩
    · simpa only [prefixValue_succ, prior] using next j
    · rw [Nat.succ_mul]
      omega

/-- One source feeds the left boundary, each internal factor adds one layer
of `q` vertices, and a final sink sums over the right boundary. -/
theorem hasABP (k : ℕ) (left right : Fin q → Affine F σ)
    (middle : Fin k → Fin q → Fin q → Affine F σ) :
    HasABP (1 + q * 2 + k * (q * (q + 1)) + (q + 1))
      (∑ j, prefixValue k (fun a => (left a).polynomial)
        (fun i a b => (middle i a b).polynomial) j * (right j).polynomial) := by
  obtain ⟨n,g,state,prior,cost⟩ := prefix_rows k left middle
  obtain ⟨n',g',state',next,cost'⟩ := g.exists_layer state (fun i (_ : Fin 1) => right i)
  refine ⟨⟨n',g',state' 0⟩,?_,?_⟩
  · change g'.values (state' 0) = _
    simpa only [prior] using next 0
  · change n' + g'.edgeCount ≤ _
    simpa only [one_mul] using cost'.trans (Nat.add_le_add_right cost (1*(q+1)))

end
end Hierarchy.ChainProduct

end OAI
