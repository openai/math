import OAI.Computability.BorderVNP.PackedHistoryDenseStep
import OAI.Computability.BorderVNP.PackedHistoryPhysicalCodec

/-! # Adaptive physical histories with sorting before every cut

The system performs the actual dense-input step on every selected child
tuple. Saving the result under new sparse names is a distinct operation.
The tensor sum below retains the public histogram enumeration of this
two-sided use of stable cable rows.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized

open Cover Crossing Packing Shortening Shortening.Adaptive
open scoped Classical

variable {D m k b : ℕ} [NeZero D] {K : Type*} [Field K] {I P : Type} [Fintype I]
    {bits : P → ℕ} {A : ℕ → Type*} {B : Fin b → Type} [∀ i, Fintype (B i)] {depth : ℕ → ℕ}
    (e : PaidIdentity K D m)
    (view : ∀ n, A n → PlacedPack D (Port k P n) (width bits k n) K I (depth n))

/-- The physical choice type at a node, before storage in the adaptive state. -/
def Choice (i : Fin b) (c : Fin k → A i.val)
    (s : Stage m (B i) (depth (i.val+1)) (fun a => view i.val (c a))) := s.Index e

/-- The attained physical output before it is saved in the next state. -/
noncomputable def physicalOutput (i : Fin b) (c : Fin k → A i.val)
    (s : Stage m (B i) (depth (i.val+1)) (fun a => view i.val (c a)))
    (hist : Choice (B := B) e view i c s) :
    PlacedPack D (Port k P (i.val+1)) (width bits k (i.val+1)) K I (depth (i.val+1)) :=
  s.result e hist

/-- A finite-height state machine with dependent branch indices and a certified save. -/
structure StateProgram (A : ℕ → Type*) (k b : ℕ)
    (Action : ∀ (i : Fin b), (Fin k → A i.val) → Type*)
    (Index : ∀ i c, Action i c → Type*)
    (Saved : ∀ i c s, Index i c s → A (i.val+1) → Prop) where
  /-- The public operation for the given tuple of actual child states. -/
  stage : ∀ i c, Action i c
  /-- New state of each attained branch. -/
  advance : ∀ i c, Index i c (stage i c) → A (i.val+1)
  /-- Physical storage correctness on that branch. -/
  sound : ∀ i c q, Saved i c (stage i c) q (advance i c q)

/-- A stored pack has the tensor, charged length, and concentration of the actual output. -/
def Saved (i : Fin b) (c : Fin k → A i.val)
    (s : Stage m (B i) (depth (i.val+1)) (fun a => view i.val (c a)))
    (q : Choice (B := B) e view i c s) (x : A (i.val+1)) : Prop :=
  let y := physicalOutput (B := B) e view i c s q
  (∀ a, (view (i.val+1) x).pack.tensor a = y.pack.tensor a) ∧
    (view (i.val+1) x).length = y.length ∧ (view (i.val+1) x).concentration = y.concentration

/-- The finite-height adaptive state machine for physical cuts after input normalization. -/
abbrev Program := StateProgram A k b
  (fun (i : Fin b) (c : Fin k → A i.val) => Stage m (B i) (depth (i.val+1)) (fun a => view i.val (c a)))
  (Choice (B := B) e view) (Saved (B := B) e view)

namespace Program

variable {e view} (F : Program (B := B) e view)

/-- The saved state retains the physical successor tensor pointwise. -/
theorem tensor (i : Fin b) (c : Fin k → A i.val) (q : Choice (B := B) e view i c (F.stage i c)) :
    ∀ x, (view (i.val+1) (F.advance i c q)).pack.tensor x = ((F.stage i c).result e q).pack.tensor x :=
  (F.sound i c q).1

/-- The saved state retains the physical successor's charged length. -/
theorem length (i : Fin b) (c : Fin k → A i.val) (q : Choice (B := B) e view i c (F.stage i c)) :
    (view (i.val+1) (F.advance i c q)).length = ((F.stage i c).result e q).length :=
  (F.sound i c q).2.1

/-- The saved state retains the physical successor's midpoint concentration. -/
theorem concentration (i : Fin b) (c : Fin k → A i.val) (q : Choice (B := B) e view i c (F.stage i c)) :
    (view (i.val+1) (F.advance i c q)).concentration = ((F.stage i c).result e q).concentration :=
  (F.sound i c q).2.2

/-- Adaptive state transitions enumerate exactly the dense-input crossing choices. -/
noncomputable def system : System k b A where
  choose j hj c := ⟨(F.stage ⟨j,hj⟩ c).Index e,inferInstance,F.advance ⟨j,hj⟩ c⟩

/-- The step identity and the actual storage adapter prove the adaptive tensor invariant. -/
theorem exact : F.system.Exact (fun n a => (view n a).pack) := by
  intro j hj c x
  let i : Fin b := ⟨j,hj⟩
  apply ((F.stage i c).tensor_sum e x).trans
  exact Finset.sum_congr (congrArg (@Finset.univ ((F.stage i c).Index e)) (Subsingleton.elim _ _))
    fun q _ => (F.tensor i c q x).symm

/-- Reconstructing and summing every adaptive histogram on the sorted layouts computes
the tensor product of the original leaves with their original free ports. -/
theorem tensor_histories (n : ℕ) (hn : n ≤ b) (a : Leaves k (A 0) n) (x : Ports (width bits k n)) :
    (parallelLeaves (fun a => (view 0 a).pack) n a).tensor x =
      ∑ q, (view n ((F.system.layer n).state ((F.system.histories n hn a).term q))).pack.tensor x :=
  F.system.tensor_histories _ F.exact n hn a x

/-- Concrete sorted-layout program with an additional dense save of each attained output.
The second sort is purely a storage reindexing and does not change the first allocation. -/
noncomputable def ofDenseClosed
    (good : ∀ n, PlacedPack D (Port k P n) (width bits k n) K I (depth n) → Prop)
    (stage : ∀ (i : Fin b) (c : Fin k → Adaptive.Program.Prepared good i.val),
      Stage m (B i) (depth (i.val+1)) (fun a => (c a).val))
    (capacity : ∀ (i : Fin b) (c : Fin k → Adaptive.Program.Prepared good i.val), (stage i c).Index e → ℕ)
    (number : ∀ (i : Fin b) (c : Fin k → Adaptive.Program.Prepared good i.val) (q : (stage i c).Index e),
      ((stage i c).result e q).pack.layout.Edge ↪ Fin (capacity i c q))
    (closed : ∀ (i : Fin b) (c : Fin k → Adaptive.Program.Prepared good i.val) (q : (stage i c).Index e),
      good (i.val+1) (((stage i c).result e q).dense (number i c q))) :
    Program (B := B) e (fun n (a : Adaptive.Program.Prepared good n) => a.val) where
  stage := stage
  advance i c q := ⟨((stage i c).result e q).dense (number i c q),closed i c q⟩
  sound i c q := ⟨((stage i c).result e q).dense_tensor (number i c q),
    ((stage i c).result e q).dense_length (number i c q),
    ((stage i c).result e q).dense_concentration (number i c q)⟩

end Program
end PackedHistoryCircuit.Normalized

end BorderVNP
end Computability
end OAI
