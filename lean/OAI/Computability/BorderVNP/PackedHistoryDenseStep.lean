import OAI.Computability.BorderVNP.DiagonalTaggedHistoryDense

/-! # A physical combining step on the stable public cable order

Before choosing blocks the public machine orders the disjoint input cables
by their sparse row IDs. Its actual placed crossing therefore acts on this
reindexed input. A different order can choose different cable ends for a
given histogram. Tensor preservation uses the exact crossing identity on the
reindexed input itself.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized

open Cover Crossing Packing Shortening CombiningStep
open scoped Classical

variable {D k d d' : ℕ} [NeZero D] {K : Type*} [Field K] {I P : Type} [Fintype I]
    {bits : P → ℕ} {B : Type} [Fintype B] {m : ℕ}

/-- All disjoint child cable names before stable sorting. -/
noncomputable abbrev raw (child : Fin k → PlacedPack D P bits K I d) :=
  parallelPacks fun i => (child i).pack

/-- Physical source for a shortening node after the input names are sorted.
The endpoint lifts belong to the slots actually selected in this order. -/
structure Stage (m : ℕ) (B : Type) [Fintype B] (d' : ℕ) (child : Fin k → PlacedPack D P bits K I d) where
  /-- Number of public input cable rows, including padding. -/
  rowCount : ℕ
  /-- Stable occupied row of each disjoint input cable. -/
  slot : (raw child).layout.Edge ↪ Fin rowCount
  /-- Measured bin name of an original cable after the chosen motions. -/
  bin : (raw child).layout.Edge → Option ((I → Deck (d'+1)) × B)
  /-- Direction permutation of the seed bins. -/
  perm : Fin D → Equiv.Perm ((I → Deck (d'+1)) × B)
  /-- Sign orientation of every old cable. -/
  positive : (raw child).layout.Edge → Bool
  /-- The canonical placement and lifts on the actual sorted interval decomposition. -/
  placed : Placement (m := m) (DirectoryCircuit.densePack (raw child) slot)
    (CutCircuit.denseBin (raw child).layout slot bin) perm I (SurfaceHost I (d'+1))

namespace Stage

variable {child : Fin k → PlacedPack D P bits K I d} (s : Stage m B d' child) (e : PaidIdentity K D m)

/-- Input actually presented to the interval allocator. -/
noncomputable abbrev input := DirectoryCircuit.densePack (raw child) s.slot

/-- The measured label read by each real cable in stable order. -/
noncomputable abbrev label := CutCircuit.denseBin (raw child).layout s.slot s.bin

/-- Source orientation at the sorted row. -/
noncomputable abbrev orient := s.positive ∘ (Names.denseSlot (raw child).layout s.slot).symm

/-- The count of full blocks at each seed in the true, sorted input layout. -/
noncomputable abbrev matched := SeedIntervals.blocks s.input.layout s.label s.perm m

omit [Field K] in
/-- Count words do not change under the stable reordering of the input cables. -/
theorem matched_eq (a : (I → Deck (d'+1)) × B) :
    s.matched a = SeedIntervals.blocks (raw child).layout s.bin s.perm m a := by
  unfold matched SeedIntervals.blocks
  simp only [input,label,DirectoryCircuit.densePack,CutCircuit.dense_count]

/-- Actual attained histograms on the sorted physical network. -/
abbrev Index := Counts e s.input s.label s.perm

/-- This successor uses the real old-band, hook, bank and residual rows
produced by the public serializer. -/
noncomputable def result (q : s.Index e) : PlacedPack D (Fin k × P) (fun z => bits z.2) K I d' where
  pack := output e s.input s.label s.perm s.orient (0,false) q
  site := s.placed.postSites s.input s.label s.perm e s.orient q
  charged := postMask s.input s.label s.perm e s.orient q
  midpoint := s.placed.outputMidpoint s.input s.label s.perm e s.orient q

set_option maxHeartbeats 1200000 in
/-- All histogram successors together equal the original disjoint input tensor.
The first equality is a permutation of input wires and the second is the
sewn crossing identity for the publicly ordered allocator. -/
theorem tensor_sum (x : Ports (fun z : Fin k × P => bits z.2)) :
    (raw child).tensor x = ∑ q : s.Index e, (s.result e q).pack.tensor x := by
  apply (Names.value_denseLayout (raw child).layout s.slot (raw child).table x).symm.trans
  apply (exact_sum e s.input s.label s.perm s.orient (0,false) x).trans
  apply Finset.sum_congr _ (fun _ _ => rfl)
  exact congrArg (@Finset.univ (s.Index e)) (Subsingleton.elim _ _)

/-- The per-profile charged length is measured on this very output. -/
theorem result_length (q : s.Index e) :
    (s.result e q).length = s.placed.result e s.input s.label s.perm s.orient q := rfl

/-- The per-profile midpoint population is measured on this very output. -/
theorem result_concentration (q : s.Index e) :
    (s.result e q).concentration = s.placed.outputConcentration s.input s.label s.perm e s.orient q := rfl

end Stage
end PackedHistoryCircuit.Normalized

end BorderVNP
end Computability
end OAI
