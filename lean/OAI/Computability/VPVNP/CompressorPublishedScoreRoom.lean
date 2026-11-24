import OAI.Computability.VPVNP.CompressorBlockHeadStability
import OAI.Computability.VPVNP.CompressorShrinkScoreOperands

/-!
# The shrinking layout bit lies beyond the published heads

The term planner starts in the old level's first scratch table. The selected
layout bit follows the motif term rows in that table. Its numerical address
therefore lies above the scalar cells at offsets 36 through 53.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PublishedScoreRoom

open BurstRAM Compression DescriptorSpace ShrinkBlockInputs
open scoped Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
variable {g w : ℕ} (X : State (a i) (packingLaneBits (a i) g)) (T : IncidenceDirectory w)
variable {pub : Fin 5 → Word w} {st : Word w} {mem : Memory w} {first : ℕ}

local notation "chosen" => selectedInputs B (BlockProgram.geometry B) i (BlockProgram.arena B i.val 0)

/-- Reading the typed old header identifies the actual term base and row count. -/
theorem of_header (start : ℕ) {L : Layout}
    (header : ShrinkHeaderReads.Header i X T start L first mem)
    (entry : LevelFields.Entry L first pub st mem)
    (afterHeader : levelStart L (first+i.val)+54 ≤ start)
    (termRoom : ShrinkInput.termEnd X start 10 < 2^w)
    (selectedFit : SelectedArena.Fits X (ShrinkInput.termHead X start) (10 : Word w)) :
    levelStart L (first+i.val)+54 ≤ ((SelectedPlan.layoutCell chosen).eval pub st mem).val := by
  let term := ShrinkInput.termHead (w := w) X start
  obtain ⟨hn,ht⟩ := ScorePackets.term_values B i X T start pub st mem (header.reads B entry) termRoom
  have word : (term.val : Word w) = term := Fin.ext (Nat.mod_eq_of_lt term.isLt)
  have stride : (10 : Word w).val = 10 := by
    change (10 : ℕ) % 2^w = 10
    exact Nat.mod_eq_of_lt (by have := header.room; omega)
  have below : term.val+SelectedArena.motifs X*10+2 < 2^w := by
    change term.val+SelectedArena.motifs X*(10 : Word w).val+3+4*SelectedArena.positions X+
      4*DemandRAM.absoluteCount X < 2^w at selectedFit
    rw [stride] at selectedFit
    omega
  exact BlockHeadStability.layoutCell_after B i (levelStart L (first+i.val)) term.val (SelectedArena.motifs X)
    (ht.trans word.symm) hn (afterHeader.trans (ScorePackets.start_le_term i X start termRoom)) below

variable (base positions blocks : ℕ)

local notation "L" => BlockProgram.layout B base positions blocks
local notation "idx" => first+i.val
local notation "start" => tableBase L idx (0 : Fin 6)

/-- The compiled table allocation supplies all address bounds, including the
room needed for the ten-word motif rows and the selected-layout score. -/
theorem allocated (header : ShrinkHeaderReads.Header i X T start L first mem)
    (entry : LevelFields.Entry L first pub st mem) (levelValid : idx < (L).levels)
    (sites : X.positions ≤ positions) (totalRoom : endAddress L < 2^w) :
    levelStart L idx+54 ≤ ((SelectedPlan.layoutCell chosen).eval pub st mem).val := by
  let amount := X.positions*ShrinkLevelSpace.tableFactor S
  have degree : 2^S.degreeExponent i.castSucc ≤ slotDegree S :=
    (Finset.le_sup (f := fun j : Fin (S.steps+1) => 2^S.degreeExponent j) (Finset.mem_univ _)).trans
      (le_max_right ..)
  have factors : ShrinkLevelSpace.tableFactor S ≤ slotDegree S*BlockProgram.fieldCount B := by
    have h : ShrinkLevelSpace.tableFactor S ≤ BlockProgram.fieldCount B :=
      (le_max_left ..).trans (Nat.le_add_right ..)
    exact h.trans (Nat.le_mul_of_pos_left _ ((Nat.two_pow_pos _).trans_le degree))
  have capacity : amount ≤ tableWords L := by
    change _ ≤ positions*slotDegree S*BlockProgram.fieldCount B
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul sites factors
  have fits := tableStop_lt L ⟨idx,levelValid⟩ (0 : Fin 6) capacity totalRoom
  have ends := ShrinkLevelSpace.packed_ends S i X start 0 0 0 w
  have termRoom := ends.2.1.trans_lt fits
  have retained : SelectedFinish.stop X (ShrinkInput.termHead (w := w) X start) (10 : Word w) < 2^w :=
    ends.2.2.1.trans_lt fits
  have selectedFit : SelectedArena.Fits X (ShrinkInput.termHead X start) (10 : Word w) :=
    ((Nat.le_add_right ..).trans (Nat.le_add_right ..) : SelectedArena.endAddr X _ _ ≤
      SelectedFinish.stop X (ShrinkInput.termHead X start) (10 : Word w)).trans_lt retained
  have afterHeader : levelStart L idx+54 ≤ start := by
    change levelStart L idx+54 ≤ levelStart L idx+66+6*slotCapacity L+0*tableWords L
    omega
  exact of_header B i X T start header entry afterHeader termRoom selectedFit

end CompressorRecords.PublishedScoreRoom

end VPVNP
end Computability
end OAI
