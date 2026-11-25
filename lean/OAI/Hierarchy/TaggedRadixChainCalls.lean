import OAI.Hierarchy.TaggedRadixBank
import OAI.Hierarchy.TaggedRadixChainSockets

namespace OAI
/-! # Installing all oracle calls of a radix chain -/

noncomputable section
namespace Hierarchy.Tagged.RadixStage

open Catalyst CatalystSubstitution ThreeFlat Routing
open scoped BigOperators Classical

variable {F : Type*} [Field F] {k p : ℕ}

/-- Seal the specified final checker on the complete chain and install every
replacement. The gap loss counts the actual number of banked calls. -/
theorem install_chain (state holes : ℕ → Type) [∀ i, Fintype (state i)] [∀ i, Fintype (holes i)]
    (N : ∀ i, Network F (state i) (state (i+1)) (holes i))
    (os : ℕ → List (Occurrence F k)) (e : ∀ i, holes i ≃ Sockets (os i)) (n : ℕ)
    (run : ∀ i, (state i → Bool) → state (i+1) → Bool)
    (reachable : ∀ i, (state i → Bool) → Prop)
    (ok : ∀ i, i ≤ n → ComputesOn (N i) (fun a => exactWeight (os i) (a ∘ (e i).symm))
      (reachable i) (run i))
    (keep : ∀ i, i ≤ n → ∀ x, reachable i x → reachable (i+1) (run i x))
    (C : BitNetwork F (Fintype.card (state (n+1)))) (feed : state 0 → Fin p ⊕ Bool)
    (start : ∀ x : Fin p → Bool, reachable 0 (Sum.elim x id ∘ feed))
    (G : ℝ) (good : ∀ o ∈ chainCalls os n, o.replacement.Gap o.target G) :
    ∃ X : Approximation F k p,
      X.size = (chain state holes N n).cells + (chain state holes N n).internal +
        C.cells + C.internal + Fintype.card (state (n+1)) + p +
        ((chainCalls os n).map (·.replacement.size)).sum ∧
      X.Gap (fun x => TypedWiring.value C (advance state run n (Sum.elim x id ∘ feed)))
        (G-2*(k:ℝ)*((chainCalls os n).length:ℝ)) := by
  let R := chain state holes N n
  let φ := fun i (z : holes i → Bool) => exactWeight (os i) (z ∘ (e i).symm)
  have semantics := (chain_computesOn state holes N φ run reachable n ok keep).1
  have ev (x : Fin p → Bool) :
      (∑ z, TypedWiring.value («seal» R C feed) (Sum.elim x z) *
        exactWeight (chainCalls os n) (z ∘ (chainSockets holes os e n).symm)) =
        TypedWiring.value C (advance state run n (Sum.elim x id ∘ feed)) := by
    simp only [exactWeight_chain]
    exact seal_contract_on R C feed (weights holes φ n) _ _ semantics x (start x)
  obtain ⟨X, bill, gap⟩ := install_output (chainCalls os n) (chainSockets holes os e n)
    («seal» R C feed) _ ev G good
  rw [seal_size] at bill
  exact ⟨X, bill, gap⟩


end Hierarchy.Tagged.RadixStage

end
end OAI
