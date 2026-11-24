import OAI.Computability.VPVNP.CompressorShrinkHeaderReads

/-!
# Reading the shrinking term header from the tight block layout

The physical scalar and pointer publishers supply the eight kinds of
metadata used by the shrinking term launches. The first scratch table
lies beyond the header, so writes to the shrinking arena preserve every
one of these cells.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkHeaderReads

open BurstRAM Compression DescriptorSpace ShrinkBlockInputs
open scoped Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
variable {R : Type*} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f)
variable {g w : ℕ} (X : State (a i) (packingLaneBits (a i) g)) (s : X.ShrinkSelection B.shrink)
variable (T : IncidenceDirectory w) (base positions blocks iteration : ℕ)
local notation "L" => BlockProgram.layout B base positions blocks
local notation "first" => (S.steps+1)*iteration
local notation "level" => first+i.val
local notation "head" => levelStart L level
/-- Index zero among the six level tables, whose published pointer gives the first shrinking
scratch address. -/
def firstTable : Fin (BlockProgram.layout B base positions blocks).shape.tables :=
  ⟨0,by change 0 < 6; decide⟩

local notation "firstIndex" => firstTable B base positions blocks
local notation "start" => tableBase L level firstIndex

theorem table_after_header : head+60 < start := by
  have hh : levelHeaderWords L = 66 := rfl
  change head+60 < head + levelHeaderWords L + 6*slotCapacity L + 0*tableWords L
  rw [hh,Nat.zero_mul]
  omega

set_option maxHeartbeats 1000000 in
theorem of_published (selector : List Bool) (dH : ℕ) (mem : Memory w)
    (fit : endAddress L < 2^w) (it : iteration < blocks)
    (published : let v : SelectedLevel B f hf :=
      ⟨_,_,_,_,X,B.shrinkPassAt f hf i rfl X,.shrink i rfl X,s,selector⟩
      LevelFields.Published L level v dH mem)
    (incidence : ∀ c, mem (incidenceHead L level c) = T.column c)
    (scratch : mem (tableHead L level firstIndex) = (start : Word w)) :
    Header i X T start L first mem := by
  have hl : level < (L).levels := by
    have h := Nat.mul_le_mul_left (S.steps+1) it
    rw [Nat.mul_succ] at h
    change (S.steps+1)*iteration+i.val < 1+(S.steps+1)*blocks
    have := i.isLt
    omega
  have hr := level_room L fit ⟨level,hl⟩
  have before := table_after_header B i base positions blocks iteration
  have next : start ≤ levelStart L (level+1) :=
    (Nat.le_add_right _ _).trans (tableEnd_le_nextLevel L level firstIndex)
  refine ⟨before.trans_le next |>.trans hr,published.vertices,published.degree,published.lanes,published.residual,?_,?_⟩
  · intro c
    have eqn : incidenceHead L level c = head+(54+c.val) := by change head+54+c.val = _; omega
    rw [← eqn]; exact incidence c
  · exact scratch

end CompressorRecords.ShrinkHeaderReads

end

end VPVNP
end Computability
end OAI
