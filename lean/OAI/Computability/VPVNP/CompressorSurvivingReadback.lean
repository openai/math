import OAI.Computability.VPVNP.CompressorShrinkSliceTable

/-!
# Reading a surviving width from its admitted term

The selected layout chooses one of two groups of four payload cells. The width
of its role is that cell plus one selector field per repetition, computed from
the repetition header of the same dense motif row.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkSliceSweep

open BurstRAM Compression Compression.PackingData ShrinkSliceArrays
open MotifBlocks MotifGrid MotifConversion ShrinkMotif

variable {w d c n N J nL : ℕ} {V H Tag L : Type}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
variable [DecidableEq V] [DecidableEq Tag] [DecidableEq L]
variable (P : PackingData V H Tag L d c) (cd : P.BundleNumbering) (site : Site V Tag L ≃ Fin n)
local notation "M" => (n*d)*pieceCount d c
variable (T : Allocation w ((n*d)*pieceCount d c) (Slots.oldBaseArcCount N J d c*nL))
variable {K : Type*} [_root_.Field K] {factor : ℝ}
variable (F : FixedBlock K demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31/16) factor)
variable (old : Arc V H Tag L d c → ℕ) (choice : ∀ m : P.Motif, P.ShrinkChoice cd old F m)

/-- Reading the repetition and payload as naturals gives the selected role's
width, including all selector bits. -/
theorem selected_width_readback (fit : T.Fits) (selectors : T.selectors.val = F.selectorBits)
    {mem : Memory w} (terms : Terms P cd site T F old choice mem) (i : Fin M) (t : Fin 4) :
    (mem (T.termStart i+1)).val*T.selectors.val +
      (mem (T.termStart i+2+T.layout.toNat*4+t.val)).val = selected P cd site T F old choice (i,t) := by
  let motif := (ShrinkMotifOrder.number P cd site).symm i
  let j := supplyRoles.symm (T.layout,t)
  obtain ⟨_,rep,payload⟩ := terms i
  have base : (Fin.ofNat (2^w) (T.termStart i)).val = T.termStart i := (T.row_vals fit (i,t)).1
  have hj := payload j
  rw [base] at rep hj
  rw [supplyRoles_index, ← Nat.add_assoc] at hj
  change (mem (T.termStart i+2+T.layout.toNat*4+t.val)).val =
    (choice motif).val (supplyRoles (supplyRoles.symm (T.layout,t))) at hj
  rw [Equiv.apply_symm_apply] at hj
  rw [rep,selectors,hj,Nat.add_comm]
  rfl

/-- The machine's word multiply and add agree with the exact selected width
whenever that output fits in a word. -/
theorem selected_width_word (fit : T.Fits) (selectors : T.selectors.val = F.selectorBits)
    {mem : Memory w} (terms : Terms P cd site T F old choice mem) (i : Fin M) (t : Fin 4)
    (bound : selected P cd site T F old choice (i,t) < 2^w) :
    (mem (T.termStart i+1)*T.selectors + mem (T.termStart i+2+T.layout.toNat*4+t.val)).val =
      selected P cd site T F old choice (i,t) := by
  rw [Fin.val_add,Fin.val_mul,Nat.mod_add_mod,
    selected_width_readback P cd site T F old choice fit selectors terms i t,Nat.mod_eq_of_lt bound]

end CompressorRecords.ShrinkSliceSweep

end VPVNP
end Computability
end OAI
