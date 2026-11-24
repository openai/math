import OAI.Computability.VPVNP.CompressorBlockCapacity

/-!
# Physical endpoints of selected shrink and refresh substeps

The static table dimensions of the block program fit the actual graph
at any level having at most the initially reserved number of positions.
Each exclusive endpoint stays within its named table, before the next
level and strictly below the machine word modulus.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.BlockLevelFit

open BurstRAM Compression DescriptorSpace ShrinkSlots SlotLevel

variable {w : ℕ} {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
variable (base positions blocks : ℕ)

/-- Natural address of the first word of table `j` in the given level's fixed-stride array
bank. -/
def tableStart (L : Layout) (level j : ℕ) := arrayBase L level + j*tableWords L

/-- Bounds placing an exclusive suballocation end inside its table, before the next level and
below the word modulus. -/
structure Endpoint (w : ℕ) (L : Layout) (level : ℕ) (j endAddr : ℕ) : Prop where
  within : endAddr ≤ tableStart L level j + tableWords L
  next : endAddr ≤ levelStart L (level+1)
  word : endAddr < 2^w

private theorem endpoint {L : Layout} (level : Fin L.levels) {j e : ℕ} (hj : j < L.shape.tables)
    (h : e ≤ tableStart L level j + tableWords L) (fit : endAddress L < 2^w) :
    Endpoint w L level.val j e := by
  have next := h.trans (tableEnd_le_nextLevel L level ⟨j,hj⟩)
  exact ⟨h,next,next.trans_lt (level_room L fit level)⟩

variable {L : Layout} (level : Fin L.levels)
local notation "head" => tableStart L level.val

/-- All seven packed arenas and both resident placements use the native
indices of the actual shrink calendar. Table zero also admits the contiguous
output and resident variants. -/
theorem shrink (physical : L = BlockProgram.layout B base positions blocks) (i : Fin S.steps) {g : ℕ}
    (X : State (S.degreeExponent i.castSucc) (packingLaneBits (S.degreeExponent i.castSucc) g))
    (size : X.positions ≤ positions) (fit : endAddress L < 2^w) :
    let a := S.degreeExponent i.castSucc
    let b := S.degreeExponent i.succ
    let sh := levelShape (b := b) X
    let term := ShrinkInput.termHead (w := w) X (head 0)
    let stride := Fin.ofNat (2^w) 10
    let role := SelectedArena.roleBase X term stride
    let selected := SelectedFinish.stop X term stride
    Endpoint w L level.val 0 (ShrinkInput.stop X (head 0)) ∧
      Endpoint w L level.val 0 (ShrinkInput.termEnd X (head 0) 10) ∧
      Endpoint w L level.val 0 selected ∧
      Endpoint w L level.val 0 (ShrinkOutput.stop (b := b) X term.val stride.val role selected) ∧
      Endpoint w L level.val 1 (head 1+ShrinkTermSelection.bundles X*
        IndexedStarts.capacity (2^(Shrink.colors a)*2^a/4) (ShrinkRankSpace.cap a)) ∧
      Endpoint w L level.val 2 (ShrinkOutput.slotsBase X (head 2) sh) ∧
      Endpoint w L level.val 3 (finish sh (ShrinkOutput.heads sh role (head 3))) ∧
      Endpoint w L level.val 0 (ShrinkResidentLayout.layout X selected).endAddr ∧
      Endpoint w L level.val 5 (ShrinkResidentLayout.layout X (head 5)).endAddr := by
  intro a b sh term stride role selected
  have capacity : X.positions * ShrinkLevelSpace.tableFactor S ≤ tableWords L := by
    rw [physical]
    unfold tableWords slotCapacity
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul size (BlockProgram.field_rates B base positions blocks).1
  have tables : L.shape.tables = 6 := physical ▸ rfl
  have bound (j : Fin 6) {n : ℕ}
      (h : n ≤ head j + X.positions*ShrinkLevelSpace.tableFactor S) : Endpoint w L level.val j n :=
    endpoint level (tables.symm ▸ j.isLt) (h.trans (Nat.add_le_add_left capacity _)) fit
  obtain ⟨h₁,h₂,h₃,h₄,h₅,h₆,h₇⟩ := ShrinkLevelSpace.packed_ends S i X (head 0) (head 1) (head 2) (head 3) w
  obtain ⟨r₀,r₅⟩ := ShrinkLevelSpace.resident_table S i X (head 0) (head 5) w
  exact ⟨bound 0 h₁,bound 0 h₂,bound 0 h₃,bound 0 h₄,bound 1 h₅,bound 2 h₆,bound 3 h₇,bound 0 r₀,bound 5 r₅⟩

/-- Table zero holds the complete refresh scratch, term, supply and output
incidence plan. Table four holds the three physical placement columns. -/
theorem refresh (physical : L = BlockProgram.layout B base positions blocks) {g : ℕ} (X : State S.portExponent (S.portExponent+g))
    (size : X.positions ≤ positions) (fit : endAddress L < 2^w) :
    let s := RefreshBlockPlan.shape B
    let plan := PortRefresh.Allocation.plan X (S.degreeExponent 0) s.dH s.ties s.stride (head 0)
    Endpoint w L level.val 0 plan.stop ∧ Endpoint w L level.val 4 (head 4+3*X.positions) := by
  intro s plan
  have posEq : plan.sites = X.positions := by
    change Fintype.card X.Base*2^S.portExponent*2^g = Fintype.card (X.Base × BitWord (S.portExponent+g))
    rw [Fintype.card_prod,Fintype.card_congr (bitWordFinEquiv _),Fintype.card_fin,pow_add,Nat.mul_assoc]
  obtain ⟨_,refreshRate,_,placement⟩ := BlockProgram.field_rates B base positions blocks
  have count : L.positions = positions := physical ▸ rfl
  have sites : plan.sites ≤ L.positions := (posEq.le.trans size).trans_eq count.symm
  have tables : L.shape.tables = 6 := physical ▸ rfl
  let zero : Fin L.shape.tables := ⟨0,by omega⟩
  have rates : 7*2^S.portExponent+s.ties+s.stride+3*s.dH+6*2^(S.degreeExponent 0) ≤ L.shape.slots*L.shape.fields := by
    rw [physical]; exact refreshRate
  have allocated := refresh_table_room (w := w) L X (S.degreeExponent 0) s.dH s.ties s.stride level zero
    sites rates fit
  have places : 3*X.positions ≤ tableWords L := by
    rw [physical]
    unfold tableWords slotCapacity
    rw [Nat.mul_comm 3,Nat.mul_assoc]
    exact Nat.mul_le_mul size placement
  exact ⟨endpoint level (by omega) allocated.1 fit,
    endpoint level (by omega) (Nat.add_le_add_left places _) fit⟩

end CompressorRecords.BlockLevelFit

end VPVNP
end Computability
end OAI
