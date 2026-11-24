import OAI.Computability.VPVNP.CompressorRecordsShrinkGreedy
import OAI.Computability.VPVNP.CompressorLogAccess

/-! # Memory used to prepare the shrinking tag operands

The first pass reads the old displacement column and writes the projected
tags. The second pass publishes their zero operand. Both label computations
can still read the old directed incidence tables afterward.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.GreedyArena.Run

open BurstRAM Compression Greedy
open scoped Fin.CommRing
open private projection_frame from OAI.Computability.VPVNP.CompressorRecordsShrinkGreedy

variable {w a g origin : ℕ} {X : ShrinkingState a g} {T : IncidenceDirectory w} {m : Memory w}
variable (r : Run X T origin m)
local notation "N" => Fintype.card X.Base
local notation "D" => (2:ℕ)^a
local notation "limit" => greedyStop origin (Fintype.card X.Base) a
local notation "project" => projectionWords T origin (Fintype.card X.Base) a g

include r in
theorem projection_access (lo : ℕ) (low : ∀ c, lo ≤ (T.column c).val) :
    LogAccess (fun z ↦ lo ≤ z ∧ z < limit) (fun z ↦ origin ≤ z ∧ z < limit)
      (ShrinkTagColumn.scan project 0 (N*D) m) := by
  obtain ⟨h₁,h₂,h₃⟩ := bounds origin N a
  change origin+N ≤ _ at h₁
  have fit := r.room
  have old : T.shift.val+N*D ≤ origin := (Nat.add_le_add_left (Nat.mul_le_mul_right D
    (Nat.le_mul_of_pos_right N (Nat.two_pow_pos (packingLaneBits a g)))) _).trans (r.old 2)
  have dst : (project 1).val = shiftBase origin N a := Nat.mod_eq_of_lt (by omega)
  apply LogAccess.mono (ShrinkTagColumn.scan_footprints project (N*D) m)
  · rintro z ⟨i,hi,rfl⟩
    change lo ≤ (T.shift + (i : Word w)).val ∧ (T.shift + (i : Word w)).val < _
    rw [Fin.val_add,Fin.val_natCast,Nat.add_mod_mod,Nat.mod_eq_of_lt (by omega)]
    exact ⟨(low 2).trans (Nat.le_add_right ..),by omega⟩
  · rintro z ⟨i,hi,rfl⟩
    change origin ≤ (project 1+(i : Word w)).val ∧ (project 1+(i : Word w)).val < _
    rw [Fin.val_add,Fin.val_natCast,Nat.add_mod_mod,dst,Nat.mod_eq_of_lt (by omega)]; omega

include r in
theorem zero_access (lo : ℕ) :
    LogAccess (fun z ↦ lo ≤ z ∧ z < limit) (fun z ↦ origin ≤ z ∧ z < limit)
      [ShrinkTagColumn.zeroRow project] := by
  have h := bounds origin N a
  change origin+N ≤ _ ∧ _ at h
  have fit := r.room
  have zero : (project 2).val = zeroCell origin N a := Nat.mod_eq_of_lt (Nat.lt_of_succ_lt fit)
  apply LogAccess.mono (ShrinkTagColumn.zero_footprints project)
  · exact fun _ hf ↦ hf.elim
  · rintro z rfl; rw [zero]; change origin ≤ shiftBase origin N a+N*D ∧ shiftBase origin N a+N*D < limit; omega

include r in
private theorem degreeFits : D < 2^w := by
  have h := bounds origin N a
  change origin+N ≤ _ ∧ _ at h
  have nd := r.old.baseFits
  have fit := r.room
  exact (Nat.le_mul_of_pos_left _ (Fintype.card_pos : 0<N)).trans_lt (nd.trans_lt (by omega))

include r in
theorem projected_incidence : T.Represents X (projectedMemory X T origin m) := by
  have h := bounds origin N a
  change origin+N ≤ _ ∧ _ at h
  exact r.old.preserve r.input fun z hz ↦ projection_frame X T origin m r.room r.projection z (by omega)

theorem color_incidence : T.Represents X r.color.post := r.old.preserve r.projected_incidence fun z hz ↦
  r.color.frame z (.inl hz)

include r in
theorem color_tables : (colorTables T origin N a).Represents X.slots.base X.baseIndex
    (projectedMemory X T origin m) := by
  have h := bounds origin N a
  change origin+N ≤ _ ∧ _ at h
  have fit := r.room
  exact tables_rep r.projected_incidence _ _ _ r.degreeFits (r.old.baseFits.trans (by omega))

theorem offset_tables : (tagTables T origin N a).Represents X.slots.base X.baseIndex r.color.post := by
  have h := bounds origin N a
  change origin+N ≤ _ ∧ _ at h
  have fit := r.room
  exact tables_rep r.color_incidence _ _ _ r.degreeFits (r.old.baseFits.trans (by omega))

end CompressorRecords.GreedyArena.Run

end VPVNP
end Computability
end OAI
