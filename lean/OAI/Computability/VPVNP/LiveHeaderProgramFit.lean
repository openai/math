import OAI.Computability.VPVNP.LiveHeaderScalarStages
import OAI.Computability.VPVNP.LiveHeaderAllocatedRuns
import OAI.Computability.VPVNP.LiveHeaderResources

/-!
# Scratch geometry of the linked live-header program

The native stages use one contiguous scratch allocation after the packed
processor headers. Its end gives a single word-size bound for all occupied
cells. Distinct copied fields have disjoint destinations, so later scans
preserve earlier decoded fields and the fixed scratch prefix.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeaderProgram

open BurstRAM LiveHeaderSchedule LiveHeaderWidths LiveHeaderDescriptors

variable {w base : ℕ} {s : Sizes}

/-- All scalar fit requirements follow from the end of the scratch allocation. -/
theorem scalarFit_of_limit (fit : limit s base ≤ 2^w) : ScalarFit w s base := by
  have h := fit
  rw [limit_eq] at h
  have hd : s.delta ≤ (s.h+1)*s.delta := by rw [Nat.succ_mul]; omega
  exact ⟨by omega, by omega, by omega, fit⟩

/-- Field capacities fit even when an empty buffer starts exactly at the
exclusive end of memory. -/
theorem field_capacity_lt (fit : limit s base ≤ 2^w) (f : Field) : s.capacity f < 2^w := by
  rw [limit_eq] at fit
  cases f <;> dsimp [Sizes.capacity] <;> omega

/-- Bound the live cut width before selecting a field. -/
theorem cut_width_le_capacity (s : Sizes) (i : ℕ) :
    CutSchedule.width (s.h+1) s.delta i ≤ s.capacity .exterior := by
  unfold CutSchedule.width Sizes.capacity
  split_ifs
  · exact Nat.mul_le_mul_right _ (Nat.sub_le ..)
  · exact Nat.zero_le _

theorem occupied_le_capacity (s : Sizes) (f : Field) (form : Shape) {W : ℕ}
    (hW : W ≤ s.capacity .exterior) : (span form W s.delta s.e s.config f).2 ≤ s.capacity f := by
  cases f <;> cases form <;> simp [span, count, exterior, exponents, config, Sizes.capacity] at * <;> omega

private theorem zero_offset_of_empty (form : Shape) (W d e c : ℕ) (f : Field)
    (h : (span form W d e c f).2 = 0) : (span form W d e c f).1 = 0 := by
  change count form W d e c f = 0 at h
  simp [span,h]

/-- Payload buffers start after the descriptor words and the unpacked
index/advice fields and end before the next component's allocation. -/
theorem dest_bounds (s : Sizes) (base : ℕ) (side : Side) (f : Field) (hf : f ≠ .padding) :
    adviceBase s base + s.advice ≤ dest s base side f ∧
      dest s base side f + s.capacity f ≤ limit s base := by
  cases side <;> cases f <;> simp [dest, limit, configBase, exponentBase, exteriorBase, Sizes.capacity] at * <;> omega

/-- Distinct allocated destinations occupy disjoint half-open ranges. -/
theorem dest_disjoint (s : Sizes) (base : ℕ) {a b : Side} {f g : Field}
    (hf : f ≠ .padding) (hg : g ≠ .padding) (hne : (a,f) ≠ (b,g)) :
    dest s base a f + s.capacity f ≤ dest s base b g ∨
      dest s base b g + s.capacity g ≤ dest s base a f := by
  cases a <;> cases b <;> cases f <;> cases g <;>
    simp [dest, configBase, exponentBase, exteriorBase, Sizes.capacity] at * <;> omega

/-- The row of public scan operands gives the constant cursor zero and
the two allocated descriptor words. -/
theorem scan_public (fit : limit s base ≤ 2^w) (side : Side) (f : Field) :
    let p := scalarPub w s base (.scan side f)
    p scanSlots.firstCursor = 0 ∧
    (p scanSlots.srcOffsetAddress).val = offsetAddr base ∧
    (p scanSlots.countAddress).val = countAddr base ∧
    p scanSlots.destinationBase = Fin.ofNat _ (dest s base side f) := by
  dsimp only
  refine ⟨rfl, ?_, ?_, rfl⟩
  · change (Fin.ofNat _ (offsetAddr base)).val = _
    apply Nat.mod_eq_of_lt
    rw [limit_eq] at fit
    unfold offsetAddr
    omega
  · change (Fin.ofNat _ (countAddr base)).val = _
    apply Nat.mod_eq_of_lt
    rw [limit_eq] at fit
    unfold countAddr
    omega

/-- The scan sizes require only the physical source extent and the allocation
bound. Its cursor starts at zero for every stage. -/
theorem scan_sizes (fit : limit s base ≤ 2^w) (side : Side) (f : Field) (iv : ℕ × ℕ)
    (hcap : iv.2 ≤ s.capacity f) (hs : iv.1 + iv.2 ≤ base) :
    LiveHeader.Allocated.Sizes scanSlots (scalarPub w s base (.scan side f)) iv (s.capacity f) := by
  have ha := fit
  rw [limit_eq] at ha
  exact ⟨(scan_public fit side f).1,hcap,field_capacity_lt fit f,by omega⟩

private theorem descriptor_before_dest (s : Sizes) (base : ℕ) (side : Side) (f : Field) (hf : f ≠ .padding) :
    countAddr base < dest s base side f ∧ offsetAddr base < dest s base side f ∧ base < dest s base side f := by
  have h := (dest_bounds s base side f hf).1
  dsimp [adviceBase,rightIndexBase,leftIndexBase,populationAddr,highAddr,indexBase,countAddr,offsetAddr] at *
  omega

/-- A full copy-stage layout at the exact public operands. For a zero-length
field the descriptor writes offset zero, including if the unused destination
address wraps at the exclusive end of memory. -/
theorem scan_copyLayout (fit : limit s base ≤ 2^w) (side : Side) (f : Field) (hf : f ≠ .padding)
    (iv : ℕ × ℕ) (hcap : iv.2 ≤ s.capacity f) (hs : iv.1 + iv.2 ≤ base)
    (h0 : iv.2 = 0 → iv.1 = 0) :
    let p := scalarPub w s base (.scan side f)
    LiveHeader.Allocated.CopyLayout scanSlots p iv ∧
      LiveHeader.Allocated.Outside (p scanSlots.destinationBase).val iv.2 base := by
  intro p
  obtain ⟨_, ho, hc, hd⟩ := scan_public fit side f
  obtain ⟨_, hmax⟩ := dest_bounds s base side f hf
  obtain ⟨hcount, hoff, hbase⟩ := descriptor_before_dest s base side f hf
  by_cases empty : iv.2 = 0
  · have hfin := (p scanSlots.destinationBase).isLt
    refine ⟨⟨by simp [empty,h0 empty], by rw [empty, Nat.add_zero]; exact hfin.le, ?_, ?_⟩, ?_⟩
    all_goals unfold LiveHeader.Allocated.Outside; omega
  · have he : (p scanSlots.destinationBase).val = dest s base side f := by
      rw [show p scanSlots.destinationBase = _ from hd]
      exact Nat.mod_eq_of_lt (by omega)
    refine ⟨⟨?_, ?_, Or.inl ?_, Or.inl ?_⟩, Or.inl ?_⟩
    · exact hs.trans (he.symm ▸ hbase.le)
    · rw [he]
      omega
    · exact (show (p scanSlots.srcOffsetAddress).val = _ from ho) ▸ he.symm ▸ hoff
    · exact (show (p scanSlots.countAddress).val = _ from hc) ▸ he.symm ▸ hcount
    · exact he.symm ▸ hbase

/-- All scan operands for a descriptor computed on an incident cut. -/
theorem scan_fit_of_shape (fit : limit s base ≤ 2^w) (side : Side) (f : Field) (tag : ℕ)
    (half firstTail : Bool) (i : ℕ) (hprefix : s.capacity .exterior ≤ base)
    (he : 1+s.e ≤ s.delta) (hc : 1+s.config ≤ s.delta) :
    let W := CutSchedule.width (s.h+1) s.delta i
    let form := shape side W tag half firstTail
    let iv := span form W s.delta s.e s.config f
    let p := scalarPub w s base (.scan side f)
    LiveHeader.Allocated.Sizes scanSlots p iv (s.capacity f) ∧
      (f ≠ .padding → LiveHeader.Allocated.CopyLayout scanSlots p iv ∧
        LiveHeader.Allocated.Outside (p scanSlots.destinationBase).val iv.2 base) := by
  intro W form iv p
  have hW := cut_width_le_capacity s i
  have hb : iv.1+iv.2 ≤ W := span_fit he hc (shape_fit (width_ge_block (s.h+1) s.delta i)) f
  have hs := hb.trans (hW.trans hprefix)
  have hcap := occupied_le_capacity s f form hW
  exact ⟨scan_sizes fit side f iv hcap hs, fun hf =>
    scan_copyLayout fit side f hf iv hcap hs (zero_offset_of_empty form W s.delta s.e s.config f)⟩

/-- A later copy retains every bit of an earlier, distinct payload field. -/
theorem preserve_copied_field {a b : Side} {f g : Field} {s : Sizes} {base : ℕ}
    (hf : f ≠ .padding) (hg : g ≠ .padding) (hne : (a,f) ≠ (b,g))
    {W : ℕ} {bits : CutSchedule.Bits W} {iv : ℕ × ℕ} {m m' : Memory w} {src len : ℕ} {slot : Fin 4}
    (hfirst : LiveHeader.CopiedSlice bits iv (dest s base a f) m) (hcap : iv.2 ≤ s.capacity f)
    (hsecond : LiveHeader.FieldCopy m slot src (dest s base b g) len m') (hcap' : len ≤ s.capacity g) :
    LiveHeader.CopiedSlice bits iv (dest s base a f) m' := by
  apply hfirst.congr
  intro j hj
  apply hsecond.frame
  rcases dest_disjoint s base hf hg hne with h | h <;> omega

/-- Copying a payload preserves the packed sites, descriptor words and all
unpacked index and advice words before the payload area. -/
theorem fieldCopy_prefix {s : Sizes} {base : ℕ} {side : Side} {f : Field} (hf : f ≠ .padding)
    {m m' : Memory w} {src len : ℕ} {slot : Fin 4}
    (hcopy : LiveHeader.FieldCopy m slot src (dest s base side f) len m') {j : ℕ}
    (hj : j < adviceBase s base + s.advice) : m' j = m j :=
  hcopy.frame j (Or.inl (hj.trans_le (dest_bounds s base side f hf).1))

end LiveHeaderProgram

end VPVNP
end Computability
end OAI
