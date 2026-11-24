import OAI.Computability.VPVNP.CompressorRecordsSelectedScoreRun
import OAI.Computability.VPVNP.CompressorRecordsDemandOutput

/-! # Consecutive score, placement and role arrays for a selected shrinking term

The two scores and the chosen layout follow the actual motif term rows.
Four old-position columns then contain the selected placement, and four
words per absolute old arc contain its demand-role record.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.SelectedArena

open Compression BurstRAM
open scoped Fin.CommRing

variable {a g w : ℕ} (X : State a (packingLaneBits a g))

/-- Number of old packed positions in this shrinking state, one for each base vertex and
packing-lane address. -/
abbrev positions := ShrinkRAM.PositionCount (Fintype.card X.Base) a g
/-- Number of selected motif term rows, counted in the physical motif order used by the score
pass. -/
abbrev motifs := (SelectedScore.motifOrder X).length

variable (termBase stride : Word w)

/-- Address immediately after the fixed-stride motif term rows, where the first layout score is
stored. -/
def origin := termBase.val + motifs X*stride.val
/-- Start of the placement columns, three words past the score origin to allow for two scores
and the chosen-layout bit. -/
def placementBase := origin X termBase stride + 3
/-- Start of the demand-role records after the four placement columns of one word per old
position. -/
def roleBase := placementBase X termBase stride + 4*positions X
/-- Exclusive end of the selected arena, after four role words for each absolute old arc. -/
def endAddr := roleBase X termBase stride + 4*DemandRAM.absoluteCount X

/-- Score-pass operands for the motif rows, selector bits, two consecutive score counters and
the layout-choice cell at offset two from the score origin. -/
def scoreTables (selectorBits : Word w) : TermScores.Tables w :=
  ⟨termBase,stride,Fin.ofNat _ (origin X termBase stride),selectorBits,Fin.ofNat _ (origin X termBase stride+2)⟩

/-- Machine-word address of the start of placement column `t`, spaced by the number of old
positions. -/
def placementWord (t : Fin 4) : Word w := Fin.ofNat _ (placementBase X termBase stride+t.val*positions X)

/-- Build the fourteen shrink-worker operands from the existing geometry and input pointers,
the selected layout word and the four placement-column addresses. -/
def shrinkWords (p₀ : Fin 14 → Word w) (layout : Word w) : Fin 14 → Word w :=
  ![p₀ 0,p₀ 1,p₀ 2,p₀ 3,p₀ 4,layout,p₀ 6,p₀ 7,p₀ 8,p₀ 9,
    placementWord X termBase stride 0,placementWord X termBase stride 1,
    placementWord X termBase stride 2,placementWord X termBase stride 3]

/-- The dynamic operand is read from the cell written by the strict score comparison. -/
def selectedWords (p₀ : Fin 14 → Word w) (m : Memory w) : Fin 14 → Word w :=
  shrinkWords X termBase stride p₀ (m (origin X termBase stride+2))

/-- Assemble the eleven demand-worker operands from shrink geometry, the old outgoing incidence
array, the selected placement columns and the role-record destination. -/
def demandWords (p₀ : Fin 14 → Word w) (T : IncidenceDirectory w) : Fin 11 → Word w :=
  ![p₀ 2,p₀ 0,p₀ 1,p₀ 3,0,T.actualOut,placementWord X termBase stride 1,
    placementWord X termBase stride 0,placementWord X termBase stride 2,
    placementWord X termBase stride 3,Fin.ofNat _ (roleBase X termBase stride)]

/-- The exclusive end of the score, placement and role arena lies strictly below the
machine-word modulus. -/
abbrev Fits := endAddr X termBase stride < 2^w

private theorem order : origin X termBase stride + 3 = placementBase X termBase stride ∧
    placementBase X termBase stride + 4*positions X = roleBase X termBase stride ∧
    roleBase X termBase stride ≤ endAddr X termBase stride := ⟨rfl,rfl,Nat.le_add_right ..⟩

theorem score_layout (selectorBits : Word w) (hstride : 10 ≤ stride.val) (fit : Fits X termBase stride) :
    TermScores.Layout (scoreTables X termBase stride selectorBits) (motifs X) (List.ofFn SelectedScore.axes) := by
  let L := scoreTables X termBase stride selectorBits
  obtain ⟨h₁,h₂,h₃⟩ := order X termBase stride
  change endAddr X termBase stride < 2^w at fit
  have hs : L.scoreBase.val = origin X termBase stride := Nat.mod_eq_of_lt (by omega)
  have hl : L.levelCell.val = origin X termBase stride+2 := Nat.mod_eq_of_lt (by omega)
  apply TermScores.Layout.ofIntervals L
  · exact (by decide : 1 < 10).trans_le hstride
  · intro axis h
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp h
    have hcoord : (SelectedScore.axes (w := w) j).coordinate.val ≤ j.val := Nat.mod_le ..
    have := j.isLt
    change 2 + (SelectedScore.axes j).coordinate.val < stride.val
    omega
  · change origin X termBase stride ≤ 2^w; omega
  · omega
  · exact Or.inl hs.ge
  · exact Or.inr (by omega)

theorem score_frame (selectorBits : Word w) (fit : Fits X termBase stride) {m out : Memory w}
    (frame : ∀ j, j ≠ (scoreTables X termBase stride selectorBits).levelCell.val →
      (∀ l, j ≠ (TermScores.counter (scoreTables X termBase stride selectorBits) l).val) → out j=m j) :
    ∀ j, j < origin X termBase stride ∨ placementBase X termBase stride ≤ j → out j=m j := by
  let L := scoreTables X termBase stride selectorBits
  obtain ⟨h₁,h₂,h₃⟩ := order X termBase stride
  change endAddr X termBase stride < 2^w at fit
  have hs : L.scoreBase.val = origin X termBase stride := Nat.mod_eq_of_lt (by omega)
  have hl : L.levelCell.val = origin X termBase stride+2 := Nat.mod_eq_of_lt (by omega)
  intro j hj
  apply frame j (by change j ≠ L.levelCell.val; omega)
  intro l
  have hb := Bool.toNat_le l
  change j ≠ (TermScores.counter L l).val
  rw [TermScores.counter,Fin.val_add,TermScores.word,Fin.val_ofNat,Nat.add_mod_mod,hs,Nat.mod_eq_of_lt (by omega)]
  omega

theorem shrink_params (p₀ : Fin 14 → Word w) {b₀ b : Bool}
    (hp : ShrinkRAM.Params p₀ a (Shrink.colors a) (Shrink.J a) g b₀)
    (m : Memory w) (hc : m (origin X termBase stride+2) = (b.toNat : Word w)) :
    ShrinkRAM.Params (selectedWords X termBase stride p₀ m) a (Shrink.colors a) (Shrink.J a) g b :=
  ⟨hp.lane,hp.tag,hp.degree,hp.mask,hp.last,by cases b <;> exact hc,hp.low_fit,hp.color_fit,hp.two_fit⟩

theorem demand_params (p₀ : Fin 14 → Word w) (T : IncidenceDirectory w) {b₀ : Bool}
    (hp : ShrinkRAM.Params p₀ a (Shrink.colors a) (Shrink.J a) g b₀) :
    BundleRAM.Params (demandWords X termBase stride p₀ T) a (Shrink.colors a) (Shrink.J a) g 0 :=
  ⟨hp.degree,hp.lane,hp.tag,hp.mask,rfl⟩

theorem inputs (p₀ : Fin 14 → Word w) (T : IncidenceDirectory w) (layout : Word w) :
    DemandRAM.Inputs (demandWords X termBase stride p₀ T) (shrinkWords X termBase stride p₀ layout) T :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem column_value (fit : Fits X termBase stride) (t : Fin 4) :
    (placementWord X termBase stride t).val = placementBase X termBase stride+t.val*positions X := by
  have h := Nat.mul_le_mul_right (positions X) t.isLt.le
  obtain ⟨_,h₂,h₃⟩ := order X termBase stride
  change endAddr X termBase stride < 2^w at fit
  exact Nat.mod_eq_of_lt (by omega)

theorem output_column (p₀ : Fin 14 → Word w) (layout : Word w) (fit : Fits X termBase stride) (t : Fin 4) :
    ((shrinkWords X termBase stride p₀ layout) (t.natAdd 10)).val =
      placementBase X termBase stride+t.val*positions X := by
  have h : shrinkWords X termBase stride p₀ layout (t.natAdd 10) = placementWord X termBase stride t := by
    fin_cases t <;> rfl
  rw [h,column_value X termBase stride fit]

/-- The old color/offset entries are indexed by base vertices, while the
mate/displacement entries are indexed by directed base slots. -/
private theorem decoded_offsets (p : Fin 14 → Word w) {l : Bool}
    (hp : ShrinkRAM.Params p a (Shrink.colors a) (Shrink.J a) g l)
    (i : Word w) (hi : i.val < positions X) :
    (ShrinkRAM.decode p i).base.val < Fintype.card X.Base ∧
      (ShrinkRAM.baseArc p (ShrinkRAM.decode p i)).val < Fintype.card X.Base * 2^a := by
  let x := (Shrink.oldIndex (a := a) (g := g) X.baseIndex).symm ⟨i.val,hi⟩
  have hx : i.val = Shrink.oldNumber X.baseIndex x := by rw [← Shrink.oldIndex_val]; simp [x]
  have dec := ShrinkRAM.decode_exact hp i
  rw [hx,Shrink.decode_oldNumber] at dec
  have hb : (ShrinkRAM.decode p i).base.val < Fintype.card X.Base := by
    rw [dec]
    exact (Nat.mod_le ..).trans_lt (X.baseIndex x.1.1).isLt
  have hs : (ShrinkRAM.decode p i).slot.val < 2^a := by
    rw [dec]
    exact (Nat.mod_le ..).trans_lt (bitWordFinEquiv a x.2.2).isLt
  refine ⟨hb,?_⟩
  have h := Nat.mul_le_mul_right (2^a) hb
  rw [Nat.succ_mul] at h
  rw [ShrinkRAM.baseArc,Fin.val_add,Fin.val_mul,hp.degree]
  exact (Nat.mod_le ..).trans_lt (by have := Nat.mod_le ((ShrinkRAM.decode p i).base.val * 2^a) (2^w); omega)

/-- The old color, offset, mate, displacement and outgoing incidence arrays all end at or
before the score origin, separating them from the new output columns. -/
structure OldInputs (p₀ : Fin 14 → Word w) (T : IncidenceDirectory w) : Prop where
  color : (p₀ 6).val + Fintype.card X.Base ≤ origin X termBase stride
  offset : (p₀ 7).val + Fintype.card X.Base ≤ origin X termBase stride
  mate : (p₀ 8).val + Fintype.card X.Base*2^a ≤ origin X termBase stride
  displacement : (p₀ 9).val + Fintype.card X.Base*2^a ≤ origin X termBase stride
  actualOut : T.actualOut.val + DemandRAM.oldCount X ≤ origin X termBase stride

theorem shrink_regions (p₀ : Fin 14 → Word w) (T : IncidenceDirectory w) (layout : Word w) {l : Bool}
    (hp : ShrinkRAM.Params (shrinkWords X termBase stride p₀ layout) a (Shrink.colors a) (Shrink.J a) g l)
    (old : OldInputs X termBase stride p₀ T) (fit : Fits X termBase stride) :
    ShrinkRAM.Regions (shrinkWords X termBase stride p₀ layout) (positions X) := by
  let p := shrinkWords X termBase stride p₀ layout
  obtain ⟨h₁,h₂,h₃⟩ := order X termBase stride
  change endAddr X termBase stride < 2^w at fit
  apply ShrinkRAM.Regions.packed p (by omega) (output_column X termBase stride p₀ layout fit)
  intro c i hi
  left
  obtain ⟨hb,ha⟩ := decoded_offsets X p hp i hi
  have h (q o : Word w) (hn : ℕ) (hq : q.val+hn ≤ origin X termBase stride) (ho : o.val<hn) :
      (q+o).val < placementBase X termBase stride := (Nat.mod_le ..).trans_lt (by omega)
  fin_cases c
  · exact h _ _ _ old.color hb
  · exact h _ _ _ old.offset hb
  · exact h _ _ _ old.mate ha
  · exact h _ _ _ old.displacement ha

theorem shrink_frame (p₀ : Fin 14 → Word w) (layout : Word w) (fit : Fits X termBase stride)
    {m : Memory w} {rs : List (Report w)}
    (h : ShrinkRAM.ScanResult (shrinkWords X termBase stride p₀ layout) (positions X) 0 (positions X) m rs) :
    ∀ addr, addr < placementBase X termBase stride ∨ roleBase X termBase stride ≤ addr →
      after m (eventLog rs) addr = m addr := by
  obtain ⟨_,h₂,h₃⟩ := order X termBase stride
  change endAddr X termBase stride < 2^w at fit
  intro addr ha
  apply h.preserve
  intro t i _ hi
  have ht := Nat.mul_le_mul_right (positions X) t.isLt
  rw [Nat.succ_mul] at ht
  rw [Nat.zero_add] at hi
  rw [ShrinkRAM.outAddr,Fin.val_add,output_column X termBase stride p₀ layout fit,
    Nat.mod_eq_of_lt (by omega)]
  omega

end CompressorRecords.SelectedArena

end

end VPVNP
end Computability
end OAI
