import OAI.Computability.BorderVNP.ShortenAdaptiveInputs
import OAI.Computability.BorderVNP.ShortenPlacedMeasurements

/-!
# Physical adaptive trees and their measured predecessor coordinates

The program at each finite stage acts on the actual K child packs. Its
state can also carry the public relative catalogs, layouts and capacity
proofs needed by the next stage. Reindexing a physical output is allowed
when it preserves its tensor, charged length and midpoint counts.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.Adaptive

open Crossing Cover Epoch Packing PlacedStep
open scoped Classical

universe u

variable {D m k b : ℕ} [NeZero D] {K : Type*} [Field K] {I P : Type} [Fintype I]
    {bits : P → ℕ} {A : ℕ → Type u} {B : Fin b → Type} [∀ i, Fintype (B i)]
    {depth : ℕ → ℕ}

variable (e : PaidIdentity K D m)
variable (view : ∀ n, A n → PlacedPack D (Port k P n) (width bits k n) K I (depth n))

/-- Actual histogram type above an indexed tuple of child states. Specifying
the finite bin instance here also fixes the template used in all saved rows. -/
def StepIndex (i : Fin b) (c : Fin k → A i.val)
    (s : PlacedStep m (B i) (depth (i.val+1)) (fun a => view i.val (c a))) :=
  PlacedStep.Index (B := B i) (P := Port k P i.val) (bits := width bits k i.val)
    (child := fun a => view i.val (c a)) s e

set_option maxHeartbeats 2000000 in
/-- The geometry and public state of an actual combining node. -/
structure Program where
  /-- The chosen physical step at each realized child tuple. -/
  step : ∀ (i : Fin b) (c : Fin k → A i.val), PlacedStep m (B i) (depth (i.val+1)) (fun a => view i.val (c a))
  /-- Save the new physical pack and its public relative information for the next step. -/
  advance : ∀ (i : Fin b) (c : Fin k → A i.val), StepIndex (B := B) e view i c (step i c) → A (i.val+1)
  /-- Storage, including any reindexing, preserves the actual tensor. -/
  tensor : ∀ (i : Fin b) (c : Fin k → A i.val) (q : StepIndex (B := B) e view i c (step i c)) (x : Ports (width bits k (i.val+1))),
    (view (i.val+1) (advance i c q)).pack.tensor x = (PlacedStep.result (child := fun a => view i.val (c a)) (B := B i) (step i c) e q).pack.tensor x
  /-- Storage preserves the charged length. -/
  length : ∀ (i : Fin b) (c : Fin k → A i.val) (q : StepIndex (B := B) e view i c (step i c)), (view (i.val+1) (advance i c q)).length = (PlacedStep.result (child := fun a => view i.val (c a)) (B := B i) (step i c) e q).length
  /-- Storage preserves the concentration of positive-length cable widths by tile. -/
  concentration : ∀ (i : Fin b) (c : Fin k → A i.val) (q : StepIndex (B := B) e view i c (step i c)), (view (i.val+1) (advance i c q)).concentration =
    (PlacedStep.result (child := fun a => view i.val (c a)) (B := B i) (step i c) e q).concentration

namespace Program

variable {e view} (F : Program (B := B) e view)

/-- The actual joint histogram is the index of each chosen successor. -/
noncomputable def system : System k b A where
  choose n hn c := ⟨(F.step ⟨n,hn⟩ c).Index e,inferInstance,F.advance ⟨n,hn⟩ c⟩

/-- Every node in the physical program computes the exact pointwise tensor
identity obtained by sorting intervals and applying the paid crossing. -/
theorem exact : F.system.Exact (fun n a => (view n a).pack) := by
  intro n hn c x
  let i : Fin b := ⟨n,hn⟩
  refine ((F.step i c).tensor_sum e x).trans ?_
  apply Finset.sum_congr _ (fun q _ => (F.tensor i c q x).symm)
  ext q
  constructor <;> intro _ <;> exact Finset.mem_univ _

/-- Every particular input tuple and its adaptive node histories satisfy the
pointwise expansion with all leaf ports retained. -/
theorem tensor_histories (n : ℕ) (hn : n ≤ b) (a : Leaves k (A 0) n) (x : Ports (width bits k n)) :
    (parallelLeaves (fun a => (view 0 a).pack) n a).tensor x =
      ∑ q, (view n ((F.system.layer n).state ((F.system.histories n hn a).term q))).pack.tensor x :=
  F.system.tensor_histories _ F.exact n hn a x

/-- Use the actual state coordinates and predecessor projections of the same
node histories that occur in the exact tensor expansion. -/
noncomputable def batch : Batch k := F.system.batch (fun n a => (view n a).length)
  (fun n a => (view n a).concentration)

/-- Both finite-stage inequalities propagate to the batch of the concrete
node histories. Here the input condition is precisely the measured physical
pair for each public histogram above the listed child states. -/
theorem stageBounds {hk : 0 < k} {r V : ℝ} {C : Fin b → ℝ}
    (rows : ∀ (i : Fin b) (c : Fin k → A i.val) (q : (F.step i c).Index e),
      let W := (∑ j, (view i.val (c j)).length) / k
      let X := childMaximum (fun j => view i.val (c j)) hk
      ((F.step i c).result e q).length / k ≤ r*W + C i * (Real.sqrt k)⁻¹ * X + C i * V ∧
      ((F.step i c).result e q).concentration / k ≤ C i * (W + (Real.sqrt k)⁻¹ * X)) :
    F.batch.StageBounds hk r V C := by
  intro i z
  let c := fun j => (F.system.layer i.val).state (z.1 j)
  let q : (F.step i c).Index e := z.2.2
  change (view (i.val+1) (F.advance i c q)).length / k ≤ _ ∧
    (view (i.val+1) (F.advance i c q)).concentration / k ≤ _
  rw [F.length i c q,F.concentration i c q]
  exact rows i c q

end Program
end Shortening.Adaptive

end BorderVNP
end Computability
end OAI
