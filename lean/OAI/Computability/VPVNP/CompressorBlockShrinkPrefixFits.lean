import OAI.Computability.VPVNP.CompressorBlockCapacity
import OAI.Computability.VPVNP.CompressorRecordsShrinkBranch
import OAI.Computability.VPVNP.CompressorDescriptorTableFits
import OAI.Computability.VPVNP.CursorDescriptorWords

/-!
# Word and instruction bounds for the shrinking prefix

The six current incidence columns end before the first scratch table. The
fixed block's table geometry holds the ten-word term array at every selected
degree. A single eventual threshold handles the capacity of the sorted
bundle totals and the arithmetic performed by the nondeterministic term
worker. Its clock is quartic in the binary input length.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkBranch

open Compression BurstRAM CursorBounds DescriptorSpace Filter
open scoped Classical

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)

/-- A common clock for the deterministic gather and every admitted shrinking
term worker, including its private opcode dispatch. -/
def prefixClock (b n : ℕ) :=
  ((SelectedTerms.shrinkGrid B).stepConstant*((b+10)^4+2)+7+ShrinkDemandGather.cost+1)*(n.log2+1)^4

theorem prefix_clock {b n M : ℕ} (hM : M ≤ n) :
    ShrinkDemandGather.cost < prefixClock B b n ∧
      TermWorker.budget B.shrink 2 8 (wordBits b n) M ≤ prefixClock B b n := by
  let L := (n.log2+1)^4
  let G := SelectedTerms.shrinkGrid B
  have hL : 1 ≤ L := pow_pos (Nat.succ_pos _) _
  have hs := (G.steps_le (wordBits b n) M).trans (Nat.mul_le_mul_left G.stepConstant (word_plus_clog_le b n M hM))
  have eqn : TermWorker.budget B.shrink 2 8 (wordBits b n) M =
      TermRecordScan.eventsPerRow G.block G.d G.e (wordBits b n) M+7 := by
    change TermWorker.budget B.shrink 2 8 _ _ = TermRecordScan.eventsPerRow B.shrink 2 8 _ _+7
    unfold TermWorker.budget TermRecordScan.eventsPerRow TermRecordScan.prepFuel; omega
  rw [eqn]
  change ShrinkDemandGather.cost < (G.stepConstant*((b+10)^4+2)+7+ShrinkDemandGather.cost+1)*L ∧
    _ ≤ (G.stepConstant*((b+10)^4+2)+7+ShrinkDemandGather.cost+1)*L
  change _ ≤ G.stepConstant*(((b+10)^4+2)*L) at hs
  rw [← Nat.mul_assoc] at hs
  have grow (x : ℕ) := Nat.le_mul_of_pos_right x hL
  simp only [Nat.add_mul,Nat.one_mul]
  have := grow 7
  have := grow ShrinkDemandGather.cost
  omega

/-- Every current incidence column, indexed with the actual row count, ends
before every scratch table, including the zeroth table. -/
theorem incidence_before (L : Layout) (w level rows : ℕ) (table : Fin L.shape.tables)
    (fits : rows ≤ slotCapacity L) (c : Fin 6) :
    ((packedIncidence L w level rows).column c).val+rows ≤ tableBase L level table := by
  rw [packed_column]
  have h := Nat.mul_le_mul_right rows c.isLt
  rw [Nat.succ_mul] at h
  have hc := h.trans (Nat.mul_le_mul_left 6 fits)
  exact (Nat.add_le_add_right (Nat.mod_le ..) _).trans (by
    change incidenceStart L level+c.val*rows+rows ≤ incidenceStart L level+6*slotCapacity L+table.val*tableWords L
    omega)

/-- In the compiled block allocation the exclusive ends of the six
incidence columns precede the term workspace. The sole ambient address
bound is that the allocated levels fit in the machine word. -/
theorem prefix_layout {a g w : ℕ} (i : Fin S.steps) (h : a = S.degreeExponent i.castSucc)
    (X : State a (packingLaneBits a g)) (base pos blocks : ℕ)
    (level : Fin (BlockProgram.layout B base pos blocks).levels)
    (positions : X.positions ≤ pos)
    (room : endAddress (BlockProgram.layout B base pos blocks) < 2^w) :
    let L := BlockProgram.layout B base pos blocks
    let T := packedIncidence L w level.val (DemandRAM.oldCount X)
    let start := tableBase L level.val (0 : Fin 6)
    (∀ c : Fin 6, (T.column c).val+DemandRAM.oldCount X ≤ start) ∧
      ShrinkInput.termEnd X start 10 < 2^w := by
  subst a
  intro L T start
  have sites : Fintype.card X.Base*2^(packingLaneBits (S.degreeExponent i.castSucc) g) = X.positions := by
    simp only [State.positions,Fintype.card_prod,Fintype.card_congr (bitWordFinEquiv _),Fintype.card_fin]
  have deg : 2^S.degreeExponent i.castSucc ≤ slotDegree S :=
    (Finset.le_sup (f := fun j : Fin (S.steps+1) => 2^S.degreeExponent j) (Finset.mem_univ _)).trans
      (le_max_right ..)
  have rs : DemandRAM.oldCount X ≤ slotCapacity L := by
    change Fintype.card X.Base*2^_*2^_ ≤ pos*slotDegree S
    rw [sites]
    exact Nat.mul_le_mul positions deg
  refine ⟨incidence_before L w level.val (DemandRAM.oldCount X) (0 : Fin 6) rs,?_⟩
  have fit := (BlockProgram.field_rates B base pos blocks).1
  have size : X.positions*ShrinkLevelSpace.tableFactor S ≤ tableWords L := by
    change _ ≤ pos*slotDegree S*BlockProgram.fieldCount B
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul positions fit
  exact (ShrinkLevelSpace.packed_ends S i X start 0 0 0 w).2.1.trans_lt (tableStop_lt L level (0 : Fin 6) size room)

private theorem prefix_numeric {a g w : ℕ} (X : State a (packingLaneBits a g))
    (T : IncidenceDirectory w) (start cap : ℕ)
    (cols : ∀ c : Fin 6, (T.column c).val+DemandRAM.oldCount X ≤ start)
    (room : ShrinkInput.termEnd X start 10 < 2^w) (ten : 10 < 2^w)
    (width : ShrinkRankSpace.cap a*X.maxWireWidth < 2^w)
    (bits : ShrinkTermSelection.fitConstant B.shrink+4*Nat.clog 2 (X.maxWireWidth+1) ≤ w)
    (gather : ShrinkDemandGather.cost < cap) (clock : TermWorker.budget B.shrink 2 8 w X.maxWireWidth ≤ cap) :
    PrefixFits B X T start (Fin.ofNat _ 10) cap := by
  have stride : (Fin.ofNat (2^w) 10).val = 10 := Nat.mod_eq_of_lt ten
  exact ⟨cols,stride.ge,by rw [stride]; exact room,width,bits,gather,clock⟩

set_option maxHeartbeats 1200000 in
/-- One input threshold works for every level, every split of the lane bits
and every allowed shrinking choice. The current position and width bounds
are exactly the bounds supplied by the selected cursor execution. -/
theorem eventually_prefixFits_at (b : ℕ) (hb : 1 ≤ b) : ∀ᶠ n : ℕ in atTop,
    ∀ (capacity : ℕ) (i : Fin S.steps) {g : ℕ}
      (X : State (S.degreeExponent i.castSucc) (packingLaneBits (S.degreeExponent i.castSucc) g)),
      X.positions ≤ capacity → X.maxWireWidth ≤ n →
      ∀ (base blocks : ℕ) (level : Fin (BlockProgram.layout B base capacity blocks).levels),
      let w := wordBits b n
      let L := BlockProgram.layout B base capacity blocks
      let T := packedIncidence L w level.val (DemandRAM.oldCount X)
      let start := tableBase L level.val (0 : Fin 6)
      endAddress L < 2^w → ∀ cap, prefixClock B b n ≤ cap → PrefixFits B X T start (Fin.ofNat _ 10) cap := by
  let Q := Finset.univ.sup fun i : Fin S.steps => ShrinkRankSpace.cap (S.degreeExponent i.castSucc)
  filter_upwards [CursorRAM.eventual_word_room b hb ((PolynomiallyBounded.const Q).mul PolynomiallyBounded.id),
    CursorRAM.eventual_word_room b hb (PolynomiallyBounded.const 10),
    DemandPreparation.eventually_live_word_fits b hb (ShrinkTermSelection.fitConstant B.shrink) 4 1 1]
    with n product ten words
  intro capacity i g X positions width base blocks level w L T start room cap enough
  have layout := prefix_layout B i rfl X base capacity blocks level positions room
  have clocks := prefix_clock B (b := b) width
  have wordFit := words X.maxWireWidth (by simpa using width)
  have q : ShrinkRankSpace.cap (S.degreeExponent i.castSucc) ≤ Q := Finset.le_sup (f := fun j : Fin S.steps => ShrinkRankSpace.cap (S.degreeExponent j.castSucc)) (Finset.mem_univ i)
  exact prefix_numeric B X T start cap layout.1 layout.2 ten ((Nat.mul_le_mul q width).trans_lt product)
    wordFit (clocks.1.trans_le enough) (clocks.2.trans enough)

/-- Specialization to the cursor's initial position capacity. -/
theorem eventually_prefixFits (b : ℕ) (hb : 1 ≤ b) : ∀ᶠ n : ℕ in atTop,
    ∀ (i : Fin S.steps) {g : ℕ}
      (X : State (S.degreeExponent i.castSucc) (packingLaneBits (S.degreeExponent i.castSucc) g)),
      X.positions ≤ initialPositions b n → X.maxWireWidth ≤ n →
      ∀ (base blocks : ℕ) (level : Fin (BlockProgram.layout B base (initialPositions b n) blocks).levels),
      let w := wordBits b n
      let L := BlockProgram.layout B base (initialPositions b n) blocks
      let T := packedIncidence L w level.val (DemandRAM.oldCount X)
      let start := tableBase L level.val (0 : Fin 6)
      endAddress L < 2^w → ∀ cap, prefixClock B b n ≤ cap → PrefixFits B X T start (Fin.ofNat _ 10) cap := by
  filter_upwards [eventually_prefixFits_at B b hb] with n run
  exact run (initialPositions b n)

/-- The chosen selector-bit constant and all four integerized relative masses
fit at one common threshold independent of the current shrinking state. -/
theorem eventually_selectionWords (b : ℕ) (hb : 1 ≤ b) : ∀ᶠ n : ℕ in atTop,
    (Fin.ofNat (2^(wordBits b n)) B.shrink.selectorBits).val = B.shrink.selectorBits ∧
      ∀ t, MotifAdmission.weight ShrinkMotif.relativeMass t < 2^(wordBits b n) := by
  let K := B.shrink.selectorBits+Finset.univ.sup (MotifAdmission.weight ShrinkMotif.relativeMass)
  filter_upwards [CursorRAM.eventual_word_room b hb (PolynomiallyBounded.const K)] with n room
  change K < 2^(wordBits b n) at room
  refine ⟨Nat.mod_eq_of_lt ((Nat.le_add_right ..).trans_lt room),fun t => ?_⟩
  exact (Finset.le_sup (f := MotifAdmission.weight ShrinkMotif.relativeMass) (Finset.mem_univ t)).trans_lt
    ((Nat.le_add_left ..).trans_lt room)

/-- The selected geometry fits the same zeroth scratch table as its term
array. Together with the two eventual word lemmas this supplies every
numerical premise of the actual shrinking-branch construction. -/
theorem selected_geometry_fit {g w : ℕ} (i : Fin S.steps)
    (X : State (S.degreeExponent i.castSucc) (packingLaneBits (S.degreeExponent i.castSucc) g))
    (base pos blocks : ℕ) (level : Fin (BlockProgram.layout B base pos blocks).levels)
    (sites : X.positions ≤ pos) (room : endAddress (BlockProgram.layout B base pos blocks) < 2^w) :
    let L := BlockProgram.layout B base pos blocks
    let start := tableBase L level.val (0 : Fin 6)
    SelectedFinish.stop X (ShrinkInput.termHead (w := w) X start) (Fin.ofNat _ 10) ≤ 2^w := by
  intro L start
  have fit := (BlockProgram.field_rates B base pos blocks).1
  have size : X.positions*ShrinkLevelSpace.tableFactor S ≤ tableWords L := by
    change _ ≤ pos*slotDegree S*BlockProgram.fieldCount B
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul sites fit
  exact ((ShrinkLevelSpace.packed_ends S i X start 0 0 0 w).2.2.1.trans_lt
    (tableStop_lt L level (0 : Fin 6) size room)).le

end CompressorRecords.ShrinkBranch

end

end VPVNP
end Computability
end OAI
