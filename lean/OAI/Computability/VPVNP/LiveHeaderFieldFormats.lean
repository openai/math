import OAI.Computability.VPVNP.LiveHeaderFieldUnitPadding

/-!
# Decoding both incident fields from a completed live header

The incident cut index determines the evaluated layout, including the pair
layout at the midpoint on the input side of the first tail group. Each
interior padding condition refers to the same bits as the typed layout.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeaderProgram.Fields

open BurstRAM CutSchedule ChainAssignments LiveHeaderSchedule LiveHeaderDescriptors LiveHeader
open scoped Fin.CommRing

variable {w t Z : ℕ} {s : Sizes} {cuts : AllCuts s.h s.delta} {g : Fin (2^(s.h+1))} {tag : Mode.Tag}

private theorem interval_at_index (s : Sizes) (g : Fin (2^(s.h+1))) (tag : Mode.Tag) (side : Side) (f : Field) :
    let i := (incidentCut side g).val
    let W := width (s.h+1) s.delta i
    interval s g tag side f = span (if W = 0 then .missing else if tag = .unit then .unit else
      if i ≤ 2^s.h then .pair else .tail) W s.delta s.e s.config f := by
  dsimp only
  dsimp only [interval, firstHalfFlag]
  rw [shape_at_group s.h (g.val+1) tag.code.val side (incidentWidth (Δ := s.delta) side g)]
  have hi : cutIndex side (g.val+1) = (incidentCut side g).val := by cases side <;> simp [incidentCut,cutIndex]
  rw [hi]
  cases tag <;> rfl

/-- A missing endpoint has no field on either side, in every mode. -/
theorem interval_endpoint (s : Sizes) (g : Fin (2^(s.h+1))) (tag : Mode.Tag) (side : Side) (f : Field)
    (endpt : (incidentCut side g).val = 0 ∨ (incidentCut side g).val = 2^(s.h+1)) :
    interval s g tag side f = (0,0) := by
  have hw : incidentWidth (Δ := s.delta) side g = 0 := by
    rcases endpt with h | h <;> simp [incidentWidth,h]
  rw [interval_at_index]
  change width (s.h+1) s.delta (incidentCut side g).val = 0 at hw
  rw [hw, ite_eq_left rfl]
  cases f <;> rfl

/-- The payload at a first-half cut uses the pair layout up to and including the midpoint. -/
theorem interval_pair (s : Sizes) (g : Fin (2^(s.h+1))) (tag : Mode.Tag) (ev : tag ≠ .unit)
    (side : Side) (f : Field) (hΔ : 0 < s.delta) (hi : 0 < (incidentCut side g).val)
    (half : (incidentCut side g).val ≤ 2^s.h) :
    interval s g tag side f = span .pair (incidentWidth (Δ := s.delta) side g) s.delta s.e 0 f := by
  rw [interval_at_index]
  have hw : width (s.h+1) s.delta (incidentCut side g).val ≠ 0 := by
    rw [width_double s.h s.delta _ hi half]; omega
  rw [ite_eq_right hw, ite_eq_right ev, ite_eq_left half]
  cases f <;> rfl

/-- Every interior cut strictly after the midpoint uses the serialized configuration layout. -/
theorem interval_tail (s : Sizes) (g : Fin (2^(s.h+1))) (tag : Mode.Tag) (ev : tag ≠ .unit)
    (side : Side) (f : Field) (hΔ : 0 < s.delta) (half : 2^s.h < (incidentCut side g).val)
    (hend : (incidentCut side g).val < 2^(s.h+1)) :
    interval s g tag side f = span .tail (incidentWidth (Δ := s.delta) side g) s.delta 0 s.config f := by
  rw [interval_at_index]
  have hw : width (s.h+1) s.delta (incidentCut side g).val ≠ 0 := by
    rw [width_tail s.h s.delta _ half.le hend]
    exact hΔ.ne'
  rw [ite_eq_right hw, ite_eq_right ev, ite_eq_right half.not_ge]
  cases f <;> rfl

/-- At each missing endpoint the padding guard is vacuous. -/
theorem validPadding_endpoint (side : Side)
    (endpt : (incidentCut side g).val = 0 ∨ (incidentCut side g).val = 2^(s.h+1)) :
    ValidPadding s cuts g tag side := by
  unfold ValidPadding
  rw [interval_endpoint s g tag side .padding endpt]
  exact fun _ _ hj _ => False.elim (Nat.not_lt_zero _ hj)

theorem validPadding_pair_iff (ev : tag ≠ .unit) (side : Side) (he : s.e = t*Z)
    (fit : 1+t*Z ≤ s.delta) (hi : 0 < (incidentCut side g).val) (half : (incidentCut side g).val ≤ 2^s.h) :
    ValidPadding s cuts g tag side ↔
      (firstHalfLayout s.h s.delta (incidentCut side g).val t Z hi half fit (cuts (incidentCut side g))).2.2.2 =
        fun _ => false := by
  unfold ValidPadding
  rw [interval_pair s g tag ev side .padding (by omega) hi half, he]
  exact Physical.pair_padding_zero hi half fit _

theorem validPadding_tail_iff (ev : tag ≠ .unit) (side : Side) (fit : 1+s.config ≤ s.delta)
    (half : 2^s.h < (incidentCut side g).val) (hend : (incidentCut side g).val < 2^(s.h+1)) :
    ValidPadding s cuts g tag side ↔
      (tailLayout s.h s.delta (incidentCut side g).val s.config half.le hend fit (cuts (incidentCut side g))).2.2 =
        fun _ => false := by
  unfold ValidPadding
  rw [interval_tail s g tag ev side .padding (by omega) half hend]
  exact Physical.tail_padding_zero half.le hend fit _

/-- Canonical trailing bits in the layout of one cut. Endpoint strings have no entries. -/
def decodedPadding (s : Sizes) (cuts : AllCuts s.h s.delta) (t Z : ℕ)
    (he : 1+t*Z ≤ s.delta) (hc : 1+s.config ≤ s.delta) (i : Fin (2^(s.h+1)+1)) : Prop :=
  if interior : 0 < i.val ∧ i.val < 2^(s.h+1) then
    if half : i.val ≤ 2^s.h then
      (firstHalfLayout s.h s.delta i.val t Z interior.1 half he (cuts i)).2.2.2 = fun _ => false
    else (tailLayout s.h s.delta i.val s.config (by omega) interior.2 hc (cuts i)).2.2 = fun _ => false
  else True

/-- The two evaluated padding guards are exactly the typed trailing-bit tests
on the incoming and outgoing cut, including endpoint and midpoint cases. -/
theorem validPadding_evaluated_iff (ev : tag ≠ .unit) (he : s.e = t*Z) (hpair : 1+t*Z ≤ s.delta)
    (htail : 1+s.config ≤ s.delta) :
    (∀ side, ValidPadding s cuts g tag side) ↔
      ∀ side, decodedPadding s cuts t Z hpair htail (incidentCut side g) := by
  apply forall_congr'
  intro side
  let i := incidentCut side g
  unfold decodedPadding
  split_ifs with interior half
  · exact validPadding_pair_iff ev side he hpair interior.1 half
  · exact validPadding_tail_iff ev side htail (Nat.lt_of_not_ge half) interior.2
  · exact iff_true_intro (validPadding_endpoint side (by have := i.isLt; dsimp [i] at *; omega))

variable {base : ℕ} {before m : Memory w}

/-- A complete image contains the occupied part of each of the six payload buffers. -/
theorem Image.copiedField (img : Image s base cuts g tag 8 before m) (side : Side) (f : Field)
    (hf : f ≠ .padding) :
    CopiedSlice (cuts (incidentCut side g)) (interval s g tag side f) (dest s base side f) m := by
  obtain ⟨k, hk⟩ := key_surj (side,f)
  let copied (p : Side × Field) := CopiedSlice (cuts (incidentCut p.1 g))
    (interval s g tag p.1 p.2) (dest s base p.1 p.2) m
  exact (congrArg copied hk).mp (img.copies k k.isLt (by simpa only [hk] using hf))

/-- An unoccupied word of a payload buffer retains its value at entry to the field suffix. -/
theorem Image.unoccupied {n : ℕ} (img : Image s base cuts g tag n before m) (side : Side) (f : Field)
    (hf : f ≠ .padding) (j : ℕ) (low : (interval s g tag side f).2 ≤ j) (high : j < s.capacity f) :
    m (dest s base side f+j) = before (dest s base side f+j) := by
  apply img.frame
  have pre := before_destination s base side f hf
  refine ⟨by omega, by unfold offsetAddr; omega, by unfold countAddr; omega, ?_⟩
  intro side' f' hf'
  by_cases same : (side,f) = (side',f')
  · rcases Prod.mk.inj same with ⟨rfl,rfl⟩
    exact Or.inr (Nat.add_le_add_left low _)
  · have cap := interval_capacity s g tag side' f'
    rcases dest_disjoint s base hf hf' same with left | right
    · exact Or.inl ((Nat.add_lt_add_left high _).trans_le left)
    · exact Or.inr (by omega)

/-- The actual buffer at either pair-format cut represents its decoded exponent vector. -/
theorem Image.pair_exponents (img : Image s base cuts g tag 8 before m) (ev : tag ≠ .unit)
    (side : Side) (he : s.e = t*Z) (fit : 1+t*Z ≤ s.delta)
    (hi : 0 < (incidentCut side g).val) (half : (incidentCut side g).val ≤ 2^s.h) :
    ExponentWords
      ((firstHalfLayout s.h s.delta (incidentCut side g).val t Z hi half fit (cuts (incidentCut side g))).2.2.1)
      (exponentBase s base side) m := by
  have copy := img.copiedField side .exponents (by decide)
  rw [interval_pair s g tag ev side .exponents (by omega) hi half, he] at copy
  exact copy.pair_exponents hi half fit

/-- The exterior scratch words contain the exact bits of the doubled primed cut. -/
theorem Image.pair_exterior (img : Image s base cuts g tag 8 before m) (ev : tag ≠ .unit)
    (side : Side) (he : s.e = t*Z) (fit : 1+t*Z ≤ s.delta)
    (hi : 0 < (incidentCut side g).val) (half : (incidentCut side g).val ≤ 2^s.h)
    (j : Fin (width (s.h+1) s.delta (2*(incidentCut side g).val))) :
    m (exteriorBase s base side+j.val) = PrimedInputRAM.encodeBit w
      ((firstHalfLayout s.h s.delta (incidentCut side g).val t Z hi half fit (cuts (incidentCut side g))).2.1 j) := by
  have copy := img.copiedField side .exterior (by decide)
  rw [interval_pair s g tag ev side .exterior (by omega) hi half, he] at copy
  exact copy.pair_exterior hi half fit j

/-- Each tail configuration word is the corresponding decoded configuration bit. -/
theorem Image.tail_config (img : Image s base cuts g tag 8 before m) (ev : tag ≠ .unit)
    (side : Side) (fit : 1+s.config ≤ s.delta)
    (half : 2^s.h < (incidentCut side g).val) (hend : (incidentCut side g).val < 2^(s.h+1))
    (j : Fin s.config) :
    m (configBase s base side+j.val) = PrimedInputRAM.encodeBit w
      ((tailLayout s.h s.delta (incidentCut side g).val s.config half.le hend fit (cuts (incidentCut side g))).2.1 j) := by
  have copy := img.copiedField side .config (by decide)
  rw [interval_tail s g tag ev side .config (by omega) half hend] at copy
  exact copy.tail_config half.le hend fit j

/-- The missing incoming cut at the first group preserves the zero exponent vector
installed before the suffix. This also applies at any intermediate suffix cursor. -/
theorem Image.first_exponents {n : ℕ} (img : Image s base cuts g tag n before m)
    (first : g.val = 0) (he : s.e = t*Z)
    (initial : ExponentWords (t := t) (Z := Z) (fun _ => 0) (exponentBase s base .left) before) :
    ExponentWords (t := t) (Z := Z) (fun _ => 0) (exponentBase s base .left) m := by
  apply initial.congr
  intro j hj
  apply img.unoccupied .left .exponents (by decide) j
  · rw [interval_endpoint s g tag .left .exponents (Or.inl first)]
    exact Nat.zero_le _
  · simpa only [Sizes.capacity, he] using hj

end LiveHeaderProgram.Fields

end VPVNP
end Computability
end OAI
