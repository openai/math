import OAI.Computability.VPVNP.CompressorSlotWidthState
import OAI.Computability.VPVNP.CompressorSlotScanFootprint

/-!
# External addresses of the shrinking width scan

The mask on the sparse width lookup bounds its offset even on arbitrary
initial row words. A dummy reads the first input word. A genuine identifier
decodes to a cell in the old-arc, edge-type and subdivision rectangle.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SlotWidthScan

open Slots SlotLevel ShrinkSlots BurstRAM BurstRAM.PrivateRAM PrimedStackRAM SourceTransport

private theorem splitNumber_lt {lanes sub old a : ℕ} (bound : a < (4*(old*sub))*lanes) :
    splitNumber lanes sub old a < old*lanes*4*sub := by
  have hl : 0 < lanes := Nat.pos_of_ne_zero (by rintro rfl; simp at bound)
  have hs : 0 < sub := Nat.pos_of_ne_zero (by rintro rfl; simp at bound)
  have ho : 0 < old := Nat.pos_of_ne_zero (by rintro rfl; simp at bound)
  let key := a/lanes
  let pair := key/sub
  have ht : pair/old < 4 := by
    change a/lanes/sub/old < 4
    rw [Nat.div_lt_iff_lt_mul ho,Nat.div_lt_iff_lt_mul hs,Nat.div_lt_iff_lt_mul hl]
    simpa only [Nat.mul_assoc] using bound
  have hm := Nat.mul_le_mul_right lanes (Nat.succ_le_of_lt (Nat.mod_lt pair ho))
  rw [Nat.succ_mul] at hm
  have hx : pair%old*lanes+a%lanes < old*lanes := by have := Nat.mod_lt a hl; omega
  have hy := Nat.mul_le_mul_right 4 (Nat.succ_le_of_lt hx)
  rw [Nat.succ_mul] at hy
  have hz : (pair%old*lanes+a%lanes)*4+pair/old < old*lanes*4 := by omega
  have hu := Nat.mul_le_mul_right sub (Nat.succ_le_of_lt hz)
  rw [Nat.succ_mul] at hu
  change ((pair%old*lanes+a%lanes)*4+pair/old)*sub+key%sub < _
  have := Nat.mod_lt key hs; omega

private theorem rowNumber_lt {n d j : ℕ} (hj : j < n*d) : rowNumber d j < n*2*d := by
  have hd : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hj)
  have hq : j/d < n := (Nat.div_lt_iff_lt_mul hd).mpr hj
  have h := Nat.mul_le_mul_right d (show j/d*2+1 ≤ n*2 by omega)
  rw [Nat.succ_mul] at h
  have := Nat.mod_lt j hd
  unfold rowNumber; omega

/-- All reads lie in the initialized endpoint-row and split-width workspace.
The only writes are the canonical outgoing widths. -/
theorem run_footprint {w : ℕ} (s : SlotLevel.Shape) (h : Heads) (splitHead : ℕ) (m : Memory w)
    (rs : List (Report w)) (twoFits : 2 < 2^w) (degreeFits : s.newDegree < 2^w)
    (lanesFit : s.lanes < 2^w) (subFit : (∑ t, s.subdivisions t) < 2^w)
    (oldFit : oldBaseArcCount s.bases s.tags s.oldDegree s.colors < 2^w)
    (input : splitHead+(oldBaseArcCount s.bases s.tags s.oldDegree s.colors*s.lanes)*4*(∑ t,s.subdivisions t)
      ≤ h.scratch) (first : splitHead < widthHead s h) (fit : finish s h < 2^w) :
    let p := widthBank s h splitHead w
    let P := ((template visit 0).instantiate w p).program
    runSegment P 43 (some 0) m (List.replicate (actualCount s) []) = some rs →
      Reads (fun a ↦ min splitHead (rowsHead s h) ≤ a ∧ a < widthHead s h) (eventLog rs) ∧
      Writes (fun a ↦ widthHead s h ≤ a ∧ a < finish s h) (eventLog rs) := by
  intro p P run
  let old := oldBaseArcCount s.bases s.tags s.oldDegree s.colors
  let sub := ∑ t, s.subdivisions t
  have fend : h.scratch+fields s ≤ rowsHead s h := Nat.le_add_right _ _
  have rend : rowsHead s h+owners s*s.newDegree ≤ inverseHead s h :=
    Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)) _
  have iend : inverseHead s h ≤ widthHead s h := by
    dsimp only [widthHead,inHead,outHead,inverseBaseHead,stopAddress,shiftsHead,targetsHead]; omega
  have endWidth : widthHead s h+actualCount s=finish s h := rfl
  have sizes := counts_add s
  have p0 : (p 0).val = s.newDegree := Nat.mod_eq_of_lt degreeFits
  have p1 : (p 1).val = s.lanes := Nat.mod_eq_of_lt lanesFit
  have p2 : (p 2).val = sub := Nat.mod_eq_of_lt subFit
  have p3 : (p 3).val = old := Nat.mod_eq_of_lt oldFit
  have p4 : (p 4).val = (4*(old*sub))*s.lanes := by
    change ((4*(old*sub))*s.lanes)%(2^w) = _
    change ((4*(old*sub))*s.lanes)*2+dummyCount s=fields s at sizes
    exact Nat.mod_eq_of_lt (by omega)
  have p5 : (p 5).val = rowsHead s h := Nat.mod_eq_of_lt (by omega : rowsHead s h < 2^w)
  have p6 : (p 6).val = splitHead := Nat.mod_eq_of_lt (by omega : splitHead < 2^w)
  have p7 : (p 7).val = widthHead s h := Nat.mod_eq_of_lt (by omega : widthHead s h < 2^w)
  apply SlotEventBounds.scan P 43 (actualCount s) (events p) (fun _ ↦ True) _ _ (native p) _ m rs trivial run
  intro j hj mem _
  let i := Fin.ofNat (2^w) j
  have hi : i.val = j := Nat.mod_eq_of_lt (by omega)
  have rr : rowNumber (p 0).val i.val < owners s*s.newDegree := by
    rw [p0,hi]; exact rowNumber_lt hj
  have hf : (p 5).val+rowNumber (p 0).val i.val < widthHead s h := by rw [p5]; omega
  have ra := row_val p i twoFits (hf.trans (by omega))
  have sa := width_eq p mem i twoFits (hf.trans (by omega))
  let a := (mem ((p 5).val+rowNumber (p 0).val i.val)).val/2
  have sf (hg : a < (p 4).val) :
      (p 6).val+splitNumber (p 1).val (p 2).val (p 3).val a < widthHead s h := by
    rw [p4] at hg
    have hidx := splitNumber_lt hg
    rw [p1,p2,p3,p6]
    change splitHead+old*s.lanes*4*sub ≤ h.scratch at input
    omega
  have haddr := (sa (fun hg ↦ (sf hg).trans (by omega))).1
  change (splitAddr p mem i).val = if a < (p 4).val then
    (p 6).val+splitNumber (p 1).val (p 2).val (p 3).val a else (p 6).val at haddr
  have lower := min_le_left splitHead (rowsHead s h)
  have lower' := min_le_right splitHead (rowsHead s h)
  have readRow : min splitHead (rowsHead s h) ≤ (row p i).val ∧ (row p i).val < widthHead s h := by
    rw [ra,p5]; rw [p5] at hf; omega
  have readSplit : min splitHead (rowsHead s h) ≤ (splitAddr p mem i).val ∧
      (splitAddr p mem i).val < widthHead s h := by
    by_cases hg : a < (p 4).val
    · rw [haddr,ite_eq_left hg,p6]; have hc := sf hg; rw [p6] at hc; omega
    · rw [haddr,ite_eq_right hg,p6]; exact ⟨lower,first⟩
  refine ⟨?_,?_,trivial⟩
  · intro x v he
    simp only [events,List.mem_append,List.mem_cons,List.mem_nil_iff,List.mem_replicate,
      Event.read.injEq,reduceCtorEq,and_false,or_false,false_or] at he
    rcases he with h|h <;> rw [h.1] <;> first | exact readRow | exact readSplit
  · intro x v he
    simp [events] at he
    change x = p 7+i ∧ _ at he
    rw [he.1,Fin.val_add,p7,hi,Nat.mod_eq_of_lt (by omega)]
    omega

end CompressorRecords.SlotWidthScan

end VPVNP
end Computability
end OAI
