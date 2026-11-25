import OAI.Computability.BorderVNP.PackedInheritedLayerCircuit
import OAI.Computability.BorderVNP.PackedLookup

/-! # Reading old and successor incidence data for a shortening epoch

Two address scans and two batched site lookups are shared by every inherited
endpoint row. The band table is the public clipped-interval circuit. No query
inspects any one-copy private factor.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Layer

open Crossing Shortening Shortening.SeedIntervals Shortening.StaticRows CellAddressCircuit
open ParseBatchSort VPVNP.VerifierNetwork PackedHistogram
open scoped Classical

variable {D m s old np seeds C C' d d' k k' w : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m)
variable {σ : Type*} [Fintype σ]

/-- All previously computed incidence and extent columns shared in this sparse pass. -/
abbrev Table (σ : Type*) (s old np seeds w : ℕ) :=
  σ ⊕ ((CellAddressViews.View s old np s × Fin w) ⊕
    ((CellAddressViews.View (siteCapacity e s seeds) (edgeCapacity e old seeds) np (siteCapacity e s seeds) × Fin w) ⊕
     (((Fin old × Band D) × CutCircuit.Result × Fin w) ⊕ ((End old np × Fin w) ⊕ (End old np × Fin w)))))

variable (oldF : CellAddressCircuit.Fields s old np C d k w σ)
variable (newF : CellAddressCircuit.Fields (siteCapacity e s seeds) (edgeCapacity e old seeds) np C' d' k' w σ)
variable (cut : Frame σ ((Fin old × Band D) × CutCircuit.Result × Fin w))
variable (work extent : Fin s → Fin w → σ)

/-- One batched lookup for all cable ends and ports, using the stable old site-name table. -/
noncomputable def prefixFrame (field : Fin s → Fin w → σ) : Frame σ (End old np × Fin w) :=
  PackedLookup.lookup (layout (Fin s) (End old np)) oldF.sites (fun v j => .input (field v j))
    (fun u j => .input (oldF.ptr u j))

/-- Exact extent or private width of the site named by a real endpoint. -/
theorem prefix_value (field : Fin s → Fin w → σ) (x : σ → Bool) (v : Fin s) (u : End old np)
    (h : value (x ∘ oldF.ptr u) = (oldF.sites v).val) :
    value (fun j => (prefixFrame oldF field).eval x (u,j)) = value (x ∘ field v) :=
  PackedLookup.lookup_value _ _ _ _ x u v h

/-- Preserve the upstream raw pins, and compute the singleton-cell starts and both site prefixes. -/
noncomputable def table : Frame σ (Table e σ s old np seeds w) :=
  (parallelFrame (Views.frame oldF) (parallelFrame (Views.frame newF)
    (parallelFrame cut (parallelFrame (prefixFrame oldF work) (prefixFrame oldF extent))))).withInput

/-- Size is additive in the actual two scans, two lookups and the one clip pass. -/
theorem table_size : (table e oldF newF cut work extent).size =
    (Views.frame oldF).size + ((Views.frame newF).size + (cut.size + ((prefixFrame oldF work).size +
      (prefixFrame oldF extent).size))) := by simp [table]

variable (occupied : Fin old → σ) (portUsed : Fin np → Bool) (successor : Fin (edgeCapacity e old seeds) → σ)

/-- Concrete wire names in the joined old/new address and clipped-interval table. -/
def tableFields : Fields (old := old) (np := np) (seeds := seeds) (d := d) (w := w) e (Table e σ s old np seeds w) where
  occupied i := .inl (occupied i)
  portUsed := portUsed
  successor i := .inl (successor i)
  pointer u j := .inl (oldF.ptr u j)
  oldView u j := .inr (.inl (.inl u,j))
  newView u j := .inr (.inr (.inl (.inl u,j)))
  cut r a j := .inr (.inr (.inr (.inl (r,a,j))))
  portWidth p j := .inl (oldF.portWidth p j)
  work u j := .inr (.inr (.inr (.inr (.inl (u,j)))))
  extent u j := .inr (.inr (.inr (.inr (.inr (u,j)))))

/-- Executable inherited operand frame assembled on the same branch's old and sewn directories. -/
noncomputable def inputs : Frame σ (Row old D np × Column d w) :=
  (source e (tableFields e oldF occupied portUsed successor)).subst (table e oldF newF cut work extent)

/-- The public two-epoch reader charges every shared lookup and scan once. -/
theorem inputs_size : (inputs e oldF newF cut work extent occupied portUsed successor).size ≤
    (table e oldF newF cut work extent).size + Fintype.card (Row old D np)*(1+d+6*w)*(30*d+16) := by
  simpa only [inputs,Frame.subst_size] using Nat.add_le_add_left
    (source_size e (tableFields e oldF occupied portUsed successor)) (table e oldF newF cut work extent).size

end Packing.Inherited.Layer

end BorderVNP
end Computability
end OAI
