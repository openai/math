import OAI.Computability.BorderVNP.ShortenPhysicalTree
import OAI.Computability.BorderVNP.ShortenAdaptiveFlatten
import OAI.Computability.BorderVNP.ShortenEpochRoundPlacedFinish

/-!
# The actual physical output at a public histogram

The history stores its computed state, which can reindex a pack. The final
motion acts directly on the network produced by the last combining step.
Its tensor and its measured costs agree with the stored state, and its
midpoints satisfy the canonical convention by construction.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.Adaptive

open BorderVNP.Packing BorderVNP.Crossing BorderVNP.Cover BorderVNP.Epoch.Round Finset
open scoped Classical

/-- The maximum over the individual input sites of a flat K^b leaf array. -/
noncomputable def maximumLeaf {k b : ℕ} (hk : 0 < k) {A : Type*} (flat : Fin (k^b) → A)
    (cost : A → ℝ) := univ.sup' ⟨⟨0,pow_pos hk _⟩,mem_univ _⟩ (fun i => cost (flat i))

/-- Every physical input leaf is bounded by the maximum over this very tuple. -/
theorem leaf_le_maximum {k b : ℕ} (hk : 0 < k) {A : Type*} (flat : Fin (k^b) → A) (cost : A → ℝ)
    (i : Fin (k^b)) : cost (flat i) ≤ maximumLeaf hk flat cost := le_sup' (fun j => cost (flat j)) (mem_univ i)

/-- A pointwise bound on the original leaf array holds at every nested leaf of the program. -/
theorem allLeaves_of_flat {k : ℕ} {A : Type*} (test : A → Prop) (b : ℕ) (flat : Fin (k^b) → A)
    (hf : ∀ i, test (flat i)) : allLeaves test b (leavesEquiv k A b flat) := by
  induction b with
  | zero => exact hf 0
  | succ n ih => exact fun i => ih (fun j => flat (copyIndex k n (i,j))) (fun j => hf _)

namespace Program

variable {I : Type} [Fintype I] {k b D m : ℕ} [NeZero D] {K : Type*} [Field K] {P : Type} {bits : P → ℕ}
    {A : ℕ → Type*} {B : Fin b → Type} [∀ i, Fintype (B i)] {depth : ℕ → ℕ}
    {e : PaidIdentity K D m} {view : ∀ n, A n → PlacedPack D (Port k P n) (width bits k n) K I (depth n)}
    (F : Program (B := B) e view)

/-- Use the installed physical layout and local tables at the final physical node. -/
noncomputable def executed : (n : ℕ) → (F.system.layer n).Name →
    PlacedPack D (Port k P n) (width bits k n) K I (depth n)
  | 0, z => view 0 z
  | j+1, z => (F.step ⟨j,z.2.1.down⟩ (fun i => (F.system.layer j).state (z.1 i))).result e z.2.2

set_option maxHeartbeats 2000000 in
/-- All measured state coordinates and the tensor survive any reindexing at storage. -/
theorem executed_coordinates (n : ℕ) (z : (F.system.layer n).Name) :
    (F.executed n z).pack.tensor = (view n ((F.system.layer n).state z)).pack.tensor ∧
    (F.executed n z).length = (view n ((F.system.layer n).state z)).length ∧
    (F.executed n z).concentration = (view n ((F.system.layer n).state z)).concentration := by
  cases n with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ j =>
    let i : Fin b := ⟨j,z.2.1.down⟩
    let c := fun a => (F.system.layer j).state (z.1 a)
    let x : (F.step i c).Index e := z.2.2
    exact ⟨funext (fun t => (F.tensor i c x t).symm),(F.length i c x).symm,(F.concentration i c x).symm⟩

/-- The actual output at every positive stage has the terminal midpoint convention. -/
theorem executed_canonical {n : ℕ} (hn : 0 < n) (z : (F.system.layer n).Name) : (F.executed n z).canonical := by
  cases n with
  | zero => omega
  | succ j => exact PlacedStep.result_canonical _ e _

/-- Attained terminal profiles for the original flat input tuple. -/
abbrev Hist (flat : Fin (k^b) → A 0) := (F.system.histories b le_rfl (leavesEquiv k (A 0) b flat)).Index

/-- Actual final placed network of an attained terminal profile. -/
noncomputable def terminal (flat : Fin (k^b) → A 0) (x : F.Hist flat) :=
  F.executed b ((F.system.histories b le_rfl (leavesEquiv k (A 0) b flat)).term x)

/-- Exact tensor expansion at the true final physical pack, with the original flat port ordering. -/
theorem terminal_tensor (flat : Fin (k^b) → A 0) (ports : Ports (fun z : Fin (k^b) × P => bits z.2)) :
    (parallelPacks (fun i => (view 0 (flat i)).pack)).tensor ports =
      ∑ x : F.Hist flat, (flattenPack b (F.terminal flat x).pack).tensor ports := by
  apply (F.system.tensor_flatHistories _ F.exact b le_rfl flat ports).trans
  apply sum_congr rfl
  intro x _
  rw [tensor_flattenPack,tensor_flattenPack]
  exact congrFun (F.executed_coordinates b ((F.system.histories b le_rfl (leavesEquiv k (A 0) b flat)).term x)).1.symm (nestedPorts bits k b ports)

end Program
end Shortening.Adaptive

end BorderVNP
end Computability
end OAI
