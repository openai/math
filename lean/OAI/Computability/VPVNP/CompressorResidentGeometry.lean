import OAI.Computability.VPVNP.CompressorShrinkResidentRun
import OAI.Computability.VPVNP.CompressorBlockCapacity

/-! # Physical table capacity for the shrinking resident group

The old absolute and role arrays are bounded by table zero and the two
resident directories are bounded by table five. A fitted block workspace
therefore supplies the required disjoint ranges and represents the selected
score cell without word truncation.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkResidentPackets

open Compression BurstRAM BlockPlanner PhaseRecipe DescriptorSpace
open ShrinkResidentRun ShrinkResidentLayout
open scoped Classical Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
  {g w : ℕ} (X : State (ShrinkBlockInputs.a i) (packingLaneBits (ShrinkBlockInputs.a i) g))
variable (base : Word w) (positions blocks : ℕ)
local notation "A" => BlockProgram.script B
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "H" => levelStart L 0

/-- Word address of the old absolute-identifier array immediately following the gathered motif
words. -/
abbrev absoluteWord {a g w : ℕ} (Y : State a (packingLaneBits a g)) (start : ℕ) : Word w :=
  let Z := ShrinkInput.plan Y start
  ((Z.gathered + Z.B*Z.Q : ℕ) : Word w)

/-- Word address of the old role array for the selected shrinking terms with ten-word records. -/
abbrev roleWord {a g w : ℕ} (Y : State a (packingLaneBits a g)) (start : ℕ) : Word w :=
  (SelectedArena.roleBase Y (ShrinkInput.termHead (w := w) Y start) (10 : Word w) : Word w)

/-- Natural address of the selected layout score cell at offset two in the shrinking term
arena. -/
abbrev scoreAddr {a g w : ℕ} (Y : State a (packingLaneBits a g)) (start : ℕ) :=
  SelectedArena.origin Y (ShrinkInput.termHead (w := w) Y start) (10 : Word w)+2

private theorem prefix_order {a g : ℕ} (Y : State a (packingLaneBits a g)) (start : ℕ) :
    let Z := ShrinkInput.plan Y start
    start ≤ Z.gathered+Z.B*Z.Q ∧ Z.gathered+Z.B*Z.Q+ShrinkTermInputs.motifCount Y ≤ ShrinkInput.stop Y start := by
  intro Z
  have motif : ShrinkTermInputs.motifCount Y = Z.B*Z.Q := ShrinkTermSelection.motifCount_eq Y
  have first : start ≤ Z.origin := by
    change start ≤ ShrinkInput.placementBase Y start + _
    rw [ShrinkInput.placementBase,GreedyArena.greedyStop_eq]
    omega
  change start ≤ Z.gathered+Z.B*Z.Q ∧ Z.gathered+Z.B*Z.Q+ShrinkTermInputs.motifCount Y ≤
    (Z.gathered+Z.rectangleSize+Z.A)+6*(Z.B*Z.Q)+2*Z.B
  have mid : Z.origin ≤ Z.gathered := by
    change Z.origin ≤ (Z.origin+2*Z.A+2*Z.B)+Z.rectangleSize
    omega
  omega

theorem geometry (old : Fin (L).levels) (size : X.positions ≤ positions) (room : endAddress L < 2^w) :
    let start := tableBase L old (0 : Fin 6)
    let arena := tableBase L old (5 : Fin 6)
    let abs : Word w := absoluteWord X start
    let roles : Word w := roleWord X start
    Areas X arena abs roles ∧ H ≤ abs.val ∧ H ≤ roles.val ∧
      levelStart L old+36 ≤ scoreAddr (w := w) X start ∧ scoreAddr (w := w) X start < arena ∧
      ShrinkInput.termEnd X start 10 < 2^w ∧ 10 < 2^w ∧ levelStart L old+66 ≤ 2^w ∧
      roles.val = SelectedArena.roleBase X (ShrinkInput.termHead (w := w) X start) (10 : Word w) := by
  intro start arena abs roles
  let Z := ShrinkInput.plan X start
  let N := Z.B*Z.Q
  let term : Word w := ShrinkInput.termHead X start
  let stride : Word w := 10
  let end0 := start+tableWords L
  have budget : X.positions*ShrinkLevelSpace.tableFactor S ≤ tableWords L := by
    change X.positions*ShrinkLevelSpace.tableFactor S ≤ positions*(BlockProgram.allocationShape B).slots*(BlockProgram.allocationShape B).fields
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul size (BlockProgram.field_rates B base.val positions blocks).1
  have ptr := (ShrinkLevelSpace.packed_ends S i X start 0 0 0 w)
  have res := (ShrinkLevelSpace.resident_table S i X start arena w).2
  have endFit : end0 < 2^w := tableStop_lt L old (0 : Fin 6) le_rfl room
  have arenaFit : (layout X arena).endAddr < 2^w := res.trans_lt (tableStop_lt L old (5 : Fin 6) budget room)
  have before : end0 ≤ arena := tableEnd_le_tableBase L old (a := (0 : Fin 6)) (b := (5 : Fin 6)) (by decide : (0 : Fin 6)<5)
  have src : ShrinkInput.stop X start ≤ end0 := ptr.1.trans (Nat.add_le_add_left budget _)
  have termCap : ShrinkInput.termEnd X start 10 ≤ end0 := ptr.2.1.trans (Nat.add_le_add_left budget _)
  have selected : SelectedFinish.stop X term stride ≤ end0 := ptr.2.2.1.trans (Nat.add_le_add_left budget _)
  have low := levelStart_mono L (Nat.zero_le old.val)
  have hbase : levelStart L old+66 ≤ start := by
    change levelStart L old+66 ≤ (levelStart L old+66)+6*slotCapacity L+0*tableWords L
    omega
  have hstart : start ≤ end0 := Nat.le_add_right ..
  have hrange := prefix_order X start
  change start ≤ Z.gathered+N ∧ Z.gathered+N+ShrinkTermInputs.motifCount X ≤ ShrinkInput.stop X start at hrange
  have absVal : abs.val=Z.gathered+N := Nat.mod_eq_of_lt (show Z.gathered+N < 2^w by omega)
  have termVal : term.val = ShrinkInput.stop X start+2*N := by
    apply Nat.mod_eq_of_lt
    change ShrinkInput.stop X start+2*N < 2^w
    change ShrinkInput.stop X start+2*N+N*10 ≤ end0 at termCap
    omega
  have upto : SelectedArena.roleBase X term stride+4*DemandRAM.absoluteCount X ≤ end0 := by
    apply le_trans _ selected
    change SelectedArena.endAddr X term stride ≤ SelectedArena.endAddr X term stride + _ + _
    omega
  have roleVal : roles.val = SelectedArena.roleBase X term stride := Nat.mod_eq_of_lt (show SelectedArena.roleBase X term stride < 2^w by omega)
  have lower : term.val ≤ SelectedArena.origin X term stride := Nat.le_add_right ..
  have split : SelectedArena.origin X term stride+2 < SelectedArena.roleBase X term stride := by
    change SelectedArena.origin X term stride+2 < SelectedArena.origin X term stride+3+4*_
    omega
  have length : (PairSimulation.LocalHistory.shrinkMotifOrder X).length = ShrinkTermInputs.motifCount X := rfl
  have all : Areas X arena abs roles := by
    refine ⟨arenaFit,?_,?_,.inl ?_,.inl ?_,by omega⟩
    · rw [absVal,length]; omega
    · rw [roleVal]; omega
    · rw [absVal,length]; omega
    · rw [roleVal]; omega
  change Areas X arena abs roles ∧ H ≤ abs.val ∧ H ≤ roles.val ∧
    levelStart L old+36 ≤ SelectedArena.origin X term stride+2 ∧ SelectedArena.origin X term stride+2 < arena ∧
    ShrinkInput.termEnd X start 10 < 2^w ∧ 10 < 2^w ∧ levelStart L old+66 ≤ 2^w ∧ roles.val=_
  rw [absVal,roleVal]
  exact ⟨all,by omega,by omega,by omega,by omega,termCap.trans_lt endFit,by omega,by omega,rfl⟩

end CompressorRecords.ShrinkResidentPackets

end

end VPVNP
end Computability
end OAI
