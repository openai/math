import OAI.Computability.VPVNP.CompressorShrinkSliceHeads
import OAI.Computability.VPVNP.CompressorShrinkABSliceTable
import OAI.Computability.VPVNP.CompressorShrinkTermPhases

/-!
# Interval tables of an admitted shrinking branch

The surviving sweep reads the physical term rows emitted by the fused term
verifier in precisely its dense bundle order. The source bits and rounded
pieces needed for AB slicing come from the other columns of that same
post-memory.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkSliceSweep

open BurstRAM Compression MotifGrid MotifBlocks MotifConversion ShrinkMotif
open scoped Classical

variable {k : Type*} [_root_.Field k] {factor : ℝ}
variable (F : FixedBlock k demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31/16) factor)
variable {a g w : ℕ} (X : State a (packingLaneBits a g))

local notation "sites" => Shrink.packedIndex (a := a) (g := g) X.baseIndex
local notation "M" => ((Fintype.card X.Base*(2^(Shrink.J a)*2^g))*2^a)*PackingData.pieceCount (2^a) (Shrink.colors a)
local notation "A" => Slots.oldBaseArcCount (Fintype.card X.Base) (2^(Shrink.J a)) (2^a) (Shrink.colors a) * 2^g

/-- Place the width rectangle and the dense interval banks after the term
rows. Use the exact common surviving layout selected by the energy comparison. -/
noncomputable def selectedAllocation (s : X.ShrinkSelection F) (term : Word w) (stride widthBase : ℕ)
    (subdiv : Fin 4 → ℕ) : Allocation w M A where
  termBase := term.val
  termStride := stride
  widthBase := widthBase
  absolute := absolute X.packingData X.shrinkNumber sites X.baseIndex (bitWordFinEquiv (Shrink.J a)) (bitWordFinEquiv g)
  subdiv := subdiv
  selectors := Fin.ofNat _ F.selectorBits
  layout := X.packingData.shrinkTermLayout F X.shrinkNumber X.packingWidth s

/-- The fused native verifier's fields are exactly the input image expected
by the surviving slice-table worker, including the two headers. -/
theorem written_terms (dense term : Word w) (stride widthBase cap : ℕ) (subdiv : Fin 4 → ℕ)
    (s : X.ShrinkSelection F) (m : Memory w) (rs : List (Report w))
    (h : ShrinkTermSelection.Written F X dense term stride cap s m rs) :
    Terms X.packingData X.shrinkNumber sites (selectedAllocation F X s term stride widthBase subdiv)
      F X.packingWidth s (after m (eventLog rs)) := by
  intro i
  let motif := (ShrinkMotifOrder.stateNumber X).symm i
  have hv := h.fields motif
  have eqn : ShrinkTermSelection.rowBase X term stride motif = Fin.ofNat (2^w) (term.val+i.val*stride) := by
    simp only [ShrinkTermSelection.rowBase,motif,Equiv.apply_symm_apply]
  rw [eqn] at hv
  exact hv

/-- Extra calls between term selection and slicing may update the chosen-layout
cell and scores. Equality at the ten term words suffices for the width sweep. -/
theorem terms_after (term : Word w) (stride widthBase : ℕ) (subdiv : Fin 4 → ℕ)
    (s : X.ShrinkSelection F) (prior next : Memory w)
    (ht : Terms X.packingData X.shrinkNumber sites (selectedAllocation F X s term stride widthBase subdiv)
      F X.packingWidth s prior)
    (frame : ∀ i : Fin M, ∀ j < 10, let base := Fin.ofNat (2^w) (term.val+i.val*stride)
      next (base.val+j) = prior (base.val+j)) :
    Terms X.packingData X.shrinkNumber sites (selectedAllocation F X s term stride widthBase subdiv)
      F X.packingWidth s next := by
  intro i
  obtain ⟨grid,rep,payload⟩ := ht i
  let b := Fin.ofNat (2^w) (term.val+i.val*stride)
  have read (j : ℕ) (h : j < 10) : next (b.val+j) = prior (b.val+j) := frame i j h
  exact ⟨(read 0 (by decide)) ▸ grid,(read 1 (by decide)) ▸ rep,
    fun j => (show next (b.val+2+j.val) = prior (b.val+2+j.val) by
      simpa only [Nat.add_assoc] using read (2+j.val) (by have := j.isLt; omega)) ▸ payload j⟩

set_option maxHeartbeats 900000 in
/-- Physical input to the width-sweep header's absolute-ID read in the same
dyadic state and dense order as the fused verifier. -/
theorem directory_for_selected (term abs : Word w) (stride widthBase : ℕ) (subdiv : Fin 4 → ℕ)
    (s : X.ShrinkSelection F) (mem : Memory w)
    (directory : MotifAbsolute.Directory X.slots X.baseIndex X.shrinkNumber abs mem) :
    let T := selectedAllocation F X s term stride widthBase subdiv
    ∀ i : Fin M, (mem (abs.val+i.val)).val = (T.absolute i).val :=
  Heads.directory_input X.slots X.baseIndex X.shrinkNumber abs mem directory

end CompressorRecords.ShrinkSliceSweep

end VPVNP
end Computability
end OAI
