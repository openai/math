import OAI.Computability.BorderVNP.PackedInheritedNamedWidthRead
import OAI.Computability.BorderVNP.PackedFrozenNodeProgram

/-! # Child width operands of the named frozen-tape node

A public parallel site row decodes into its child and original row. Its work
and extent fields alias the assigned width bits of that child. The same
child valuation supplies the physical geometry. The private program at the
parallel input has exactly the incoming width certified by its lineage.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape

open ParseBatchSort Shortening.PublicParallel WorkWords VPVNP.VerifierNetwork
open scoped Classical

variable {σ : Type*} {k V w : ℕ}

/-- A work or extent bit at the public flat site row, selected from the
corresponding child's shared geometry-and-width input rectangle. -/
def childWidth {Geo : Type} (pin : Fin k → WithWidths Geo V w → σ) (extent : Bool)
    (z : Fin (k*V)) (bit : Fin w) : σ :=
  let a := finProdFinEquiv.symm z
  pin a.1 (.inr (a.2,extent,bit))

/-- Every flattened public slot selects its own child, site, field and bit. -/
theorem childWidth_flat {Geo : Type} (pin : Fin k → WithWidths Geo V w → σ) (extent : Bool)
    (i : Fin k) (z : Fin V) (bit : Fin w) :
    childWidth pin extent (flat i z) bit = pin i (.inr (z,extent,bit)) := by
  simp only [childWidth,flat,Equiv.symm_apply_apply]

/-- Every actual assigned child width is recovered without gates; vacant
public names remain zero across the disjoint flat array. -/
theorem childWidth_covers {Geo : Type} [Fintype Geo] [Fintype σ] {X : Fin k → Type*}
    (pin : Fin k → WithWidths Geo V w → σ) (extent : Bool) (x : σ → Bool)
    (names : ∀ i, X i ↪ Fin V) (amount : ∀ i, X i → ℕ)
    (h : ∀ i,WorkWords.Covers (names i) (amount i) (assignedColumn extent) (x ∘ pin i)) :
    WorkWords.Covers (parallelName names) (fun z => amount z.1 z.2)
      (Frame.initial (fun z : Fin (k*V) × Fin w => childWidth pin extent z.1 z.2)) x := by
  constructor
  · rintro ⟨i,v⟩
    change value (fun j => (Frame.initial _).eval x (flat i (names i v),j)) = _
    simpa only [Frame.initial_eval,childWidth_flat,assignedColumn,Function.comp_apply] using (h i).live v
  · intro z hz
    obtain ⟨⟨i,row⟩,rfl⟩ := finProdFinEquiv.surjective z
    have hole : row ∉ Set.range (names i) := fun hr => hz ((parallelName_mem names i row).mpr hr)
    change value (fun j => (Frame.initial _).eval x (flat i row,j)) = 0
    simpa only [Frame.initial_eval,childWidth_flat,assignedColumn,Function.comp_apply] using (h i).hole row hole

/-- The full flattened input column is a projection of existing pins. -/
theorem childWidth_frame_size {Geo : Type} [Fintype σ] (pin : Fin k → WithWidths Geo V w → σ) (extent : Bool) :
    (Frame.initial (fun z : Fin (k*V) × Fin w => childWidth pin extent z.1 z.2)).size = 0 := rfl

end Packing.Inherited.FrozenTape

namespace PackedHistoryCircuit.Normalized.SourcePath.NamedRun

open Crossing Cover Epoch Epoch.Round Shortening Shortening.Adaptive Shortening.StaticRows Shortening.PublicParallel
open Packing Packing.Inherited Packing.Inherited.WorkWords Packing.Inherited.FrozenTape
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

universe u
variable {D m b k np : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
variable {e : PaidIdentity K D m} {h H ν : ℝ} {src : SourcePath b e h H ν} {last high : ℕ}
variable {V E : ℕ → ℕ} {w : ℕ} {cap : ℕ → ℕ} {Extra : ℕ → Type u}
variable {keep : ∀ j, src.NamedAt last high V E w P bits k Extra j → Prop}
variable (i : Fin b) (c : Fin k → NamedState.Admissible (src.NamedGood last high V E w cap keep) i.val)
variable (old : ∀ j,Site.Programs (c j).val.placed.pack.layout)
variable (header : WorkWords.Ports np) (leaf : P ↪ Fin np) (bound : ℕ → ℕ)
variable {σ : Type*} (x : σ → Bool)
variable (pin : Fin k → WithWidths (src.StatePins last high V E w i.val) (V i.val) w → σ)
variable (previous : ∀ j, WidthRead header leaf bound i.val (c j) (old j) (x ∘ pin j))
include previous

/-- On every genuine named child valuation the flat raw parallel pack has
exactly the work, extent and incoming operands required by the frozen node's
image theorem. The child geometry is the original named geometry. -/
theorem frozen_node_widths :
    let p := raw (fun j => (c j).val.placed)
    let names := parallelName (fun j => (c j).val.names.sites)
    let states (v : p.layout.Site) := (old v.1 v.2).program
    (∀ j, x ∘ pin j ∘ Sum.inl = (c j).val.words) ∧
    (∀ v : p.layout.Site, ParseBatchSort.value (x ∘ childWidth pin false (names v)) = (states v).work) ∧
    (∀ v : p.layout.Site, ParseBatchSort.value (x ∘ childWidth pin true (names v)) = (states v).size) ∧
    ∀ v : p.layout.Site,(states v).incoming = incoming p.layout v := by
  intro p names states
  refine ⟨fun j => (previous j).geometry,?_,?_,?_⟩
  · rintro ⟨j,v⟩
    have read := ((previous j).widths false).live v
    change ParseBatchSort.value (fun z => x (childWidth pin false (flat j ((c j).val.names.sites v)) z)) = _
    simpa only [childWidth_flat,assignedColumn,VPVNP.VerifierNetwork.Frame.initial_eval,Function.comp_apply,
      Bool.false_eq_true,ite_false] using read
  · rintro ⟨j,v⟩
    have read := ((previous j).widths true).live v
    change ParseBatchSort.value (fun z => x (childWidth pin true (flat j ((c j).val.names.sites v)) z)) = _
    simpa only [childWidth_flat,assignedColumn,VPVNP.VerifierNetwork.Frame.initial_eval,Function.comp_apply,
      ite_true] using read
  · rintro ⟨j,v⟩
    exact (old j v).size.trans ((Inherited.Parallel.incoming_eq (fun j => (c j).val.placed.pack.layout) j v).symm)

/-- The assigned work and extent both read zero on a vacant public parallel row. -/
theorem frozen_width_hole (field : Bool) (row : Fin (k*V i.val))
    (vacant : row ∉ Set.range (parallelName fun j => (c j).val.names.sites)) :
    ParseBatchSort.value (x ∘ childWidth pin field row) = 0 := by
  obtain ⟨⟨j,a⟩,rfl⟩ := finProdFinEquiv.surjective row
  have ha : a ∉ Set.range (c j).val.names.sites :=
    fun h => vacant ((parallelName_mem (fun j => (c j).val.names.sites) j a).mpr h)
  change ParseBatchSort.value (fun bit => x (childWidth pin field (flat j a) bit)) = 0
  simpa only [childWidth_flat,assignedColumn,VPVNP.VerifierNetwork.Frame.initial_eval,Function.comp_apply] using
    ((previous j).widths field).hole a ha

end PackedHistoryCircuit.Normalized.SourcePath.NamedRun

end BorderVNP
end Computability
end OAI
