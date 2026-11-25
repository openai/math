import OAI.Computability.BorderVNP.PackedInheritedLayerEndpoints
import OAI.Computability.BorderVNP.PackedOldDirectory

/-! # Genuine source of the old interval lengths and starts

The physical cut pass runs on the old sparse names and uses their dense order.
Its start and span columns are exactly those of the saved presentation consumed
by the subsequent combining operation.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Layer

open Crossing Shortening Shortening.SeedIntervals CutCircuit DirectoryCircuit ParseBatchSort VPVNP.VerifierNetwork
open scoped Classical

variable {D M m : ℕ} [NeZero D] {K P : Type*} {A : Type} {bits : P → ℕ} (pack : Pack D P bits K)
variable (slot : pack.layout.Edge ↪ Fin M) (bin : pack.layout.Edge → Option A)
variable (perm : Fin D → Equiv.Perm A)

/-- Renaming a bin changes neither the clipped start, the span, nor the selected ordinal. -/
theorem live_prior (sourceName name : A → ℕ) (z : pack.layout.Edge) (b : Band D) (r : CutCircuit.Result) :
    r.read (liveDescriptor pack.layout slot bin perm m sourceName z b) =
    r.read (priorDescriptor (m := m) (densePack pack slot) (denseBin pack.layout slot bin) perm name
      (Names.denseSlot pack.layout slot z) b) := by
  have label : denseBin pack.layout slot bin (Names.denseSlot pack.layout slot z) = bin z := by simp [denseBin]
  cases hz : bin z with
  | none =>
    rw [live_frozen _ _ _ _ _ _ z hz b]
    unfold priorDescriptor
    split
    · rfl
    · rename_i a h
      cases h.symm.trans (label.trans hz)
  | some a =>
    rw [live_charged _ _ _ _ _ _ z a hz b]
    unfold priorDescriptor
    split
    · rename_i h
      cases h.symm.trans (label.trans hz)
    · rename_i c h
      obtain rfl := Option.some.inj (h.symm.trans (label.trans hz))
      cases r <;> rfl

/-- The clipped public operand frame for all dense-save sites is fixed before the
old layout, private tables, placement and branch are supplied. -/
theorem exists_priorFrame (D m : ℕ) [NeZero D] (hm : 0 < m) :
    ∃ C E : ℕ, ∀ (M k w : ℕ) {A : Type} {σ : Type*} [Fintype A] [Fintype σ]
      (p : PublicPopulation.Pins (Fin M) σ k w) (code : A ↪ Fin (2^k)) (perm : Fin D → Equiv.Perm A),
      ∃ f : Frame σ ((Fin M × Band D) × CutCircuit.Result × Fin w),
        f.size ≤ (PublicPopulation.offsets p).size +
          PoolCircuit.scatterCost (Fintype.card A) M D C E k w +
          M*Fintype.card (Band D)*(48*w)+1+M*Fintype.card (Band D)*(3300*(w+1)^2) ∧
        ∀ {K P : Type*} {bits : P → ℕ} (pack : Pack D P bits K) (slot : pack.layout.Edge ↪ Fin M)
          (bin : pack.layout.Edge → Option A) (name : A → ℕ) (x : σ → Bool),
          PublicPopulation.Represents p pack.layout bin slot code x →
          (∀ a, count pack.layout bin a < 2^w) → (∀ z, value (x ∘ p.width (slot z)) = pack.layout.width z) →
          ∀ z b r, value (fun j => f.eval x ((denseRows pack.layout slot z,b),r,j)) =
            r.read (priorDescriptor (m := m) (densePack pack slot) (denseBin pack.layout slot bin) perm name z b) := by
  obtain ⟨C,E,frames⟩ := live_cut_frames D m hm
  refine ⟨C,E,?_⟩
  intro M k w A σ _ _ p code perm
  obtain ⟨f,hf,he⟩ := frames M k w p code perm
  refine ⟨f,hf,?_⟩
  intro K P bits pack slot bin name x rep cap widths z b r
  obtain ⟨u,rfl⟩ := (Names.denseSlot pack.layout slot).surjective z
  have h := (he pack.layout bin slot x rep cap widths u b r).trans
    (live_prior (m := m) pack slot bin perm (fun a => (code a).val) name u b r)
  simpa [denseRows] using h

end Packing.Inherited.Layer

end BorderVNP
end Computability
end OAI
