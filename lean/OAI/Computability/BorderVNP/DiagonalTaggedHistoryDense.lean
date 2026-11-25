import OAI.Computability.BorderVNP.DiagonalTaggedHistoryStorage
import OAI.Computability.BorderVNP.PackedOldDirectory

/-! # Saving an adaptive physical step in stable public row order

The directory stores only live cable rows, ordered by their public
addresses. A row permutation carries its charge and midpoint with it.
The tensor, total charged length and the full vector of tile populations
are consequently preserved before preparing the next round.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PlacedPack

open Crossing Cover Epoch Packing CombiningStep
open scoped BigOperators Classical

variable {D d r : ℕ} {P I : Type} [Fintype I] {bits : P → ℕ} {K : Type*}
    (p : PlacedPack D P bits K I d) (number : p.pack.layout.Edge ↪ Fin r)

/-- Save the placed pack in the same live row order used by the public
directory, retaining the host site, charge and midpoint of each real cable. -/
noncomputable def dense : PlacedPack D P bits K I d where
  pack := DirectoryCircuit.densePack p.pack number
  site := p.site
  charged := p.charged ∘ (Names.denseSlot p.pack.layout number).symm
  midpoint := p.midpoint ∘ (Names.denseSlot p.pack.layout number).symm

/-- Every external tensor entry survives the actual dense save. -/
theorem dense_tensor [CommSemiring K] (x : Ports bits) :
    (p.dense number).pack.tensor x = p.pack.tensor x :=
  Names.value_denseLayout p.pack.layout number p.pack.table x

/-- Original endpoint coordinates at the stable live row. -/
theorem dense_endpoints (c : p.pack.layout.Edge) :
    (p.dense number).pack.layout.src (Names.denseSlot p.pack.layout number c) = p.pack.layout.src c ∧
    (p.dense number).pack.layout.dst (Names.denseSlot p.pack.layout number c) = p.pack.layout.dst c :=
  ⟨Names.src_slot p.pack.layout _ _ c, Names.dst_slot p.pack.layout _ _ c⟩

/-- The dense row keeps the original integral bit width. -/
theorem dense_width (c : p.pack.layout.Edge) :
    (p.dense number).pack.layout.width (Names.denseSlot p.pack.layout number c) = p.pack.layout.width c :=
  Names.width_slot p.pack.layout _ _ c

/-- The physical charge and chosen midpoint are carried at the saved row. -/
theorem dense_marks (c : p.pack.layout.Edge) :
    (p.dense number).charged (Names.denseSlot p.pack.layout number c) = p.charged c ∧
    (p.dense number).midpoint (Names.denseSlot p.pack.layout number c) = p.midpoint c := by
  exact ⟨congrArg p.charged ((Names.denseSlot p.pack.layout number).symm_apply_apply c),
    congrArg p.midpoint ((Names.denseSlot p.pack.layout number).symm_apply_apply c)⟩

/-- The charged length on the quotient host is preserved cable by cable. -/
theorem dense_length : (p.dense number).length = p.length := by
  unfold length chargedLength
  refine (Fintype.sum_equiv (Names.denseSlot p.pack.layout number) _ _ fun c => ?_).symm
  rw [(p.dense_marks number c).1, p.dense_width number c,
    (p.dense_endpoints number c).1, (p.dense_endpoints number c).2]
  rfl

/-- The positive-length and charged test with the actual chosen midpoint
selects exactly the old cable at each tile. -/
theorem dense_occupies (t : I → Deck (d+1)) (c : p.pack.layout.Edge) :
    (p.dense number).occupies t (Names.denseSlot p.pack.layout number c) ↔ p.occupies t c := by
  unfold occupies
  rw [(p.dense_marks number c).1, (p.dense_endpoints number c).1,
    (p.dense_endpoints number c).2, (p.dense_marks number c).2]
  rfl

/-- Each tile retains its exact integral population of positive-length
charged widths, including all boundary midpoint choices. -/
theorem dense_population (t : I → Deck (d+1)) :
    testedWidth (p.dense number).pack.layout.width ((p.dense number).occupies t) =
      testedWidth p.pack.layout.width (p.occupies t) := by
  unfold testedWidth
  refine (Fintype.sum_equiv (Names.denseSlot p.pack.layout number) _ _ fun c => ?_).symm
  rw [p.dense_occupies number t c, p.dense_width number c]

/-- The physical concentration read by the next round is identical. -/
theorem dense_concentration : (p.dense number).concentration = p.concentration := by
  unfold concentration
  simp_rw [p.dense_population number]

end Shortening.PlacedPack

namespace Shortening.Adaptive.Program

open Crossing

variable {D m k b : ℕ} [NeZero D] {K : Type*} [Field K] {I P : Type} [Fintype I]
    {bits : P → ℕ} {B : Fin b → Type} [∀ i, Fintype (B i)] {depth : ℕ → ℕ}
    (e : PaidIdentity K D m)
    (good : ∀ n, PlacedPack D (Port k P n) (width bits k n) K I (depth n) → Prop)
    (step : ∀ (i : Fin b) (c : Fin k → Prepared good i.val),
      PlacedStep m (B i) (depth (i.val+1)) (fun j => (c j).val))
    (size : ∀ (i : Fin b) (c : Fin k → Prepared good i.val), (step i c).Index e → ℕ)
    (number : ∀ (i : Fin b) (c : Fin k → Prepared good i.val) (q : (step i c).Index e),
      ((step i c).result e q).pack.layout.Edge ↪ Fin (size i c q))
    (closed : ∀ (i : Fin b) (c : Fin k → Prepared good i.val) (q : (step i c).Index e),
      good (i.val+1) (((step i c).result e q).dense (number i c q)))

/-- The actual successor is the densely saved output, using the live row
numbers derived at this histogram. Geometric closure only specifies the
admissible prepared states for the following step. -/
noncomputable def ofDenseClosed : Program (B := B) e (fun n (p : Prepared good n) => p.val) where
  step := step
  advance i c q := ⟨((step i c).result e q).dense (number i c q), closed i c q⟩
  tensor i c q x := ((step i c).result e q).dense_tensor (number i c q) x
  length i c q := ((step i c).result e q).dense_length (number i c q)
  concentration i c q := ((step i c).result e q).dense_concentration (number i c q)

/-- The saved successor of this concrete program supplies its tagged
history adapter at every node and histogram. -/
noncomputable def denseClosedStorage :
    Diagonal.CellEntries.ProgramStorage (ofDenseClosed e good step size number closed) :=
  fun i c q => Diagonal.CellEntries.Storage.dense ((step i c).result e q).pack.layout (number i c q)

end Shortening.Adaptive.Program

end BorderVNP
end Computability
end OAI
