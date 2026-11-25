import OAI.Computability.BorderVNP.ResidueEntryBudget
import OAI.Computability.BorderVNP.ResidueEntryOutput

/-! # The complete Boolean entry verifier satisfies the polynomial budget -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ResidueEntryBudget

open VPVNP ResidueFourier ResidueEntryInput ResidueEntryOutput ResidueEntryVerifierCore
open ExactQuantumFactoring BooleanNetwork ResidueEntryField

variable {σ J K : Type*} [Fintype σ] [Fintype J] [Field K]
  {idx D d w m b p dag : ℕ} [Fact p.Prime] [Algebra (ZMod p) K]

/-- Bound the actual numbered tape verifier using its gate-free grid, threshold and
column address routing, the index preprocessor, and the shared arithmetic DAG. -/
theorem joint_count (q H width : ℕ) (B : Module.Basis (Fin d) (ZMod p) K) (hp : p < 2^w)
    (C : Circuit K (GadgetInput σ idx J m) dag) (u : Fin D → K)
    (π : Fin D → K →ₗ[ZMod p] ZMod p) :
    (verifier B hp C (fieldNet (b := b) q H width B u) (valid p) yNet (project w B π)).net.count ≤
      jointBudget (Fintype.card (Option σ)) idx D d w (Fintype.card J) m dag := by
  let h := Fintype.card (Option σ)
  have hb := build_count B hp C (fieldNet (b := b) q H width B u)
    (valid p) yNet (project w B π) (ResidueEntryInput.budget h idx D d w) (fieldNet_count q H width B u)
  have hv := valid_count (σ := σ) (idx := idx) (D := D) (J := J) (m := m)
    (d := d) (w := w) (b := b) p
  have hπ := project_count (σ := σ) (idx := idx) (J := J) (m := m) (b := b) (w := w) B π
  simp only [yNet_count,Nat.add_zero,gadget_card] at hb
  apply hb.trans
  dsimp only [jointBudget,guardBudget,projectBudget,h]
  exact Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add (Nat.add_le_add_left hv _) hπ) _) _

/-- A DAG gate upper bound controls both the instantiated Boolean circuit and its
complete serialized advice on the exact query and guess types. -/
theorem joint_resources (q H width k : ℕ) (B : Module.Basis (Fin d) (ZMod p) K) (hp : p < 2^w)
    (C : Circuit K (GadgetInput σ idx J m) dag) (u : Fin D → K)
    (π : Fin D → K →ₗ[ZMod p] ZMod p) (hk : dag ≤ k) :
    let g := (verifier B hp C (fieldNet (b := b) q H width B u) (valid p) yNet (project w B π)).net.count
    let h := Fintype.card (Option σ)
    let L := Fintype.card J
    let T := jointBudget h idx D d w L m k
    g ≤ T ∧ adviceBits (Fintype.card (Query σ idx D J m)) (Fintype.card (Guess σ d w b)) g ≤
      adviceBits (queryWidth h idx D L m) (guessWidth h d w b) T := by
  dsimp only
  have h := (joint_count (b := b) q H width B hp C u π).trans (jointBudget_mono_dag _ _ _ _ _ _ _ hk)
  refine ⟨h,?_⟩
  rw [ResidueEntryInput.query_card,ResidueEntryInput.guess_card]
  exact adviceBits_mono _ _ h

end ResidueEntryBudget

end BorderVNP
end Computability
end OAI
