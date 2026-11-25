import OAI.Hierarchy.ProbeStageRecordROM
import OAI.Hierarchy.ProbeStageAdviceROM

namespace OAI
/-! # A single fixed advised tape for the complete native subdivision -/

namespace Hierarchy.ProbeStage.Native
open Computability.VPVNP.BurstRAM
open scoped Fin.CommRing

abbrev ArrayCell (h d : ℕ) := Fin (rounds d) × Fin 16 × Fin (regionSize h d)

def ArrayCell.address {h d : ℕ} (a : ArrayCell h d) := region h d a.1.val a.2.1+a.2.2.val

private theorem phase_mono {h d i j : ℕ} (ij : i≤j) : phase h d copies i≤phase h d copies j :=
  Nat.mul_le_mul_right _ (Nat.add_le_add_left (Nat.mul_le_mul_right _ ij) _)

theorem ArrayCell.low {h d : ℕ} (a : ArrayCell h d) : phase h d copies a.1.val≤a.address := by
  unfold address region bankBase
  omega

theorem ArrayCell.high {h d : ℕ} (a : ArrayCell h d) : a.address<phase h d copies (a.1.val+1) := by
  have low := Nat.add_lt_add_left a.2.2.isLt (region h d a.1.val a.2.1)
  exact low.trans_le ((region_end h d a.1.val a.2.1).trans
    ((Nat.le_add_right _ _).trans (output_end h d copies a.1.val)))

theorem ArrayCell.injective {h d : ℕ} : Function.Injective (address (h:=h) (d:=d)) := by
  rintro a b eq
  have je : a.1=b.1 := by
    rcases lt_trichotomy a.1 b.1 with lt|same|gt
    · exact False.elim ((a.high.trans_le ((phase_mono lt).trans b.low)).ne eq)
    · exact same
    · exact False.elim ((b.high.trans_le ((phase_mono gt).trans a.low)).ne eq.symm)
  have interv {x y : ArrayCell h d} (j : x.1=y.1) (c : x.2.1<y.2.1) : x.address<y.address := by
    unfold address
    rw [j]
    exact (Nat.add_lt_add_left x.2.2.isLt _).trans_le
      ((region_separate h d y.1.val c).trans (Nat.le_add_right _ _))
  have ke : a.2.1=b.2.1 := by
    rcases lt_trichotomy a.2.1 b.2.1 with lt|same|gt
    · exact False.elim ((interv je lt).ne eq)
    · exact same
    · exact False.elim ((interv je.symm gt).ne eq.symm)
  have off : a.2.2=b.2.2 := by
    unfold address at eq
    rw [je,ke] at eq
    exact Fin.ext (Nat.add_left_cancel eq)
  exact Prod.ext je (Prod.ext ke off)

private theorem geom_low {h d : ℕ} (x : GeometryCell h d) :
    phase h d copies x.1.val≤x.address copies := by
  unfold GeometryCell.address bankBase
  omega

private theorem geom_stop {h d : ℕ} (x : GeometryCell h d) :
    x.address copies<bankBase h d copies x.1.val 11 := by
  have delta := separate h d copies x.1.val (3+x.2.1.val) 11 (by omega)
  exact (Nat.add_lt_add_left x.2.2.isLt _).trans_le delta

private theorem geom_high {h d : ℕ} (x : GeometryCell h d) :
    x.address copies<phase h d copies (x.1.val+1) := by
  have before := separate h d copies x.1.val 11 (stride d copies-9) (by unfold stride;omega)
  have end_ := output_end h d copies x.1.val
  change _≤output h d copies x.1.val at before
  have stop := geom_stop x
  omega

theorem ArrayCell.ne_geometry {h d : ℕ} (a : ArrayCell h d) (x : GeometryCell h d) :
    a.address≠x.address copies := by
  rcases lt_trichotomy a.1 x.1 with lt|eq|gt
  · exact (a.high.trans_le ((phase_mono lt).trans (geom_low x))).ne
  · have before := (geom_stop x).trans_le (Nat.le_of_lt (show bankBase h d copies x.1.val 11 <
        region h d x.1.val a.2.1 by
      have positive : 0<extent h d := pow_pos (by decide) _
      simp only [region,bankBase]
      omega))
    have dst := Nat.le_add_right (region h d a.1.val a.2.1) a.2.2.val
    rw [← eq] at before
    exact (before.trans_le dst).ne.symm
  · exact ((geom_high x).trans_le ((phase_mono gt).trans a.low)).ne.symm

noncomputable def inputTape (h d w : ℕ) (input : Memory w) : Memory w :=
  Function.extend (ArrayCell.address (h:=h) (d:=d))
    (fun a => (arrayValue h d a.1.val a.2.1 a.2.2.val : Word w)) (geometryTape h d copies w input)

theorem inputTape_array {h d w : ℕ} (m : Memory w) (a : ArrayCell h d) :
    inputTape h d w m a.address=(arrayValue h d a.1.val a.2.1 a.2.2.val : Word w) :=
  ArrayCell.injective.extend_apply _ _ _

theorem inputTape_geometry {h d w : ℕ} (m : Memory w) (x : GeometryCell h d) :
    inputTape h d w m (x.address copies)=(x.value : Word w) := by
  unfold inputTape
  rw [Function.extend_apply' _ _ _ (fun ⟨a,e⟩ => a.ne_geometry x e)]
  exact geometryTape_cell m x

theorem inputTape_root {h d w : ℕ} (m : Memory w) {i : ℕ} (lo : i<2^h) :
    inputTape h d w m i=m i := by
  have ep : 0<extent h d := pow_pos (by decide) _
  have nr : 2^h ≤ extent h d := Nat.pow_le_pow_right (by decide) (by unfold roomBits;omega)
  have first : i<3*extent h d := by omega
  unfold inputTape
  rw [Function.extend_apply' _ _ _ (by
    rintro ⟨a,rfl⟩
    have start := (phase_mono (h:=h) (d:=d) (Nat.zero_le a.1.val)).trans a.low
    simp only [phase,Nat.zero_mul,Nat.add_zero] at start
    omega)]
  exact geometryTape_prefix m first

/-- Higher-address caller data is already resident when subdivision starts. -/
theorem inputTape_above {h d w : ℕ} (m : Memory w) {a : ℕ} (high : heapEnd h d copies≤a) :
    inputTape h d w m a=m a := by
  have end_ (j : Fin (rounds d)) : phase h d copies (j.val+1)≤a :=
    (phase_in_heap j.isLt).trans high
  unfold inputTape
  rw [Function.extend_apply' _ _ _ (fun ⟨x,eq⟩ => (x.high.trans_le (end_ x.1)).ne eq)]
  unfold geometryTape
  exact Function.extend_apply' _ _ _ (fun ⟨x,eq⟩ => ((geom_high x).trans_le (end_ x.1)).ne eq)

theorem inputTape_words (h d : ℕ) :
    Fintype.card (ArrayCell h d)+Fintype.card (GeometryCell h d) =
      ((rounds d*16*(288*d+17)+rounds d*8)*4^(rounds d+1))*2^h := by
  rw [geometry_words]
  simp only [ArrayCell,Fintype.card_prod,Fintype.card_fin,regionSize,extent,room_slots]
  ring

end Hierarchy.ProbeStage.Native

end OAI
