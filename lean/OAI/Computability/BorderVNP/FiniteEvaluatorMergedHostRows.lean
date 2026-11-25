import OAI.Computability.BorderVNP.FiniteEvaluatorMergedOwned
import OAI.Computability.BorderVNP.FiniteEvaluatorReportFactors
import OAI.Computability.BorderVNP.FiniteEvaluatorPrepareReportsReady
import OAI.Computability.BorderVNP.DiagonalNativeCellProduct

/-! # Field host factors from the actual owned-row RAM

The signed dispatch scans global call rows. The field scanner traverses compact
local rows. Both products use the same physical cell, by the rank computed from
the stored owner column. The local matrix comes from the bit-major report bank.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.Reports

open VPVNP.BurstRAM RoutingISA RoutingISA.CellPacket.Supplement TeamRAM
open scoped Classical BigOperators

variable {F : Type*} [Field F] [Fintype F] {Orig : Type} {w : ℕ}

/-- The product of native signed validators on the physical global owner scan,
expressed in the compact local rank of each true seven-word task row. -/
theorem owned_product (l : TypedTaskBuilder.Layout) (raw : ℕ → ℕ) (m : Memory w)
    (value : ℕ → ℤ) (owners : ∀ c < l.cells, (m (l.call c)).val=l.owner raw c) :
    let f := (⟨l.team,l.calls,l.cells⟩ : CellDispatch.Frame)
    ((f.ownedRows m 0 f.count).map (fun c => value (l.before raw c))).prod =
      ∏ i : Fin (l.before raw l.cells), value i.val := by
  intro f
  have addr (i : Fin f.count) : f.address i.val=l.call i.val := by
    simp [f,CellDispatch.Frame.address,TypedTaskBuilder.Layout.call,Nat.add_comm,Nat.mul_comm]
  have eq := f.ownedRows_product m (Equiv.refl (Fin l.cells)) (fun c => value (l.before raw c))
    (fun c => l.owner raw c.val) (fun c => value (l.before raw c.val))
    (fun i => (addr i) ▸ owners i.val i.isLt) (fun _ _ => rfl)
  refine eq.trans ?_
  change (∏ c : Fin l.cells, if l.owner raw c.val=l.team then value (l.before raw c.val) else 1)=_
  rw [← Finset.prod_filter,Finset.prod_subtype (p:=fun c : Fin l.cells => l.owner raw c.val=l.team) _ (by simp)]
  exact (TypedTaskBuilder.ownedOrder l raw).prod_comp (fun i => value i.val)

/-- The signed validator and scalar products on the true RAM have one joint
factor for each local ownership ordinal. -/
theorem hostFactor_rows (l : TypedTaskBuilder.Layout) (raw : ℕ → ℕ) (owned : ℕ → Batch.Owned Orig)
    (supplied : ℕ → List Bool) (digits : ℕ → ℕ) (claims : ∀ i, FiniteScalarRounds.Index F → Fin (digits i) → Bool)
    (pub : Arg → Word w) (m : Memory w) (frame : CellDispatch.Frame.ofMemory pub m=⟨l.team,l.calls,l.cells⟩)
    (owners : ∀ c < l.cells, (m (l.call c)).val=l.owner raw c) :
    (inputs l raw owned supplied digits claims).hostFactor pub m =
      ∏ i : Fin (l.before raw l.cells), ((TypedBatch.cellInput (owned i.val).placed).weight : F) *
        Merged.reportScalar (digits i.val) (claims i.val) := by
  rw [Cells.Inputs.hostFactor,frame]
  let count := l.before raw l.cells
  let validator := fun i => (TypedBatch.cellInput (owned i).placed).weight
  change (((((⟨l.team,l.calls,l.cells⟩ : CellDispatch.Frame).ownedRows m 0 l.cells).map
      (fun c => validator (l.before raw c))).prod : ℤ) : F) *
      ((List.range count).map (fun i => Merged.reportScalar (digits i) (claims i))).prod=_
  rw [owned_product l raw m validator owners,Int.cast_prod]
  have rng : List.range count=List.ofFn (fun i : Fin count => i.val) := by
    apply List.ext_getElem <;> simp
  rw [rng,List.map_ofFn,List.prod_ofFn,← Finset.prod_mul_distrib]
  rfl

/-- Exact host factors at the true memory returned by the supplemental splice.
The global owner words used here were written by the task producer and
survive the actual splice. -/
theorem hostFactor_after_splice (l : TypedTaskBuilder.Layout) (raw : ℕ → ℕ) (owned : ℕ → Batch.Owned Orig)
    (supplied : ℕ → List Bool) (digits : ℕ → ℕ) (claims : ∀ i, FiniteScalarRounds.Index F → Fin (digits i) → Bool)
    (pub : Arg → Word w) (m : Memory w) (published : readings m=l.published raw)
    (apart : MetaOutside l (l.before raw l.cells) owned) {n : ℕ}
    (ready : Cells.Prepared (inputs l raw owned supplied digits claims) pub
      (Batch.written m (fun j => (owned j).cell) (l.before raw l.cells)) n) :
    let after := Batch.written m (fun j => (owned j).cell) (l.before raw l.cells)
    (inputs l raw owned supplied digits claims).hostFactor pub after =
      ∏ i : Fin (l.before raw l.cells), ((TypedBatch.cellInput (owned i.val).placed).weight : F) *
        Merged.reportScalar (digits i.val) (claims i.val) := by
  intro after
  apply hostFactor_rows
  · unfold CellDispatch.Frame.ofMemory
    rw [show (pub 0).val=l.frame from ready.pointer]
    congr 1
    · exact ready.fields.outer.1
    · exact ready.fields.outer.2.2.1
    · exact ready.fields.outer.2.2.2.1
  · intro c hc
    have kept := Batch.preserve m (fun j => (owned j).cell) (i:=0) (Nat.zero_le (l.before raw l.cells))
      (l.call c) (fun j _ hj => ((apart j hj).2.2 c hc).2)
    change readings after (l.call c)=_
    rw [show readings after (l.call c)=readings m (l.call c) from congrArg Fin.val kept,published]
    exact l.published_owner raw ready.room hc

end FiniteEvaluator.Reports

end BorderVNP
end Computability
end OAI
