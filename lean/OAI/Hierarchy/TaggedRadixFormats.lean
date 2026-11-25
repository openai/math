import OAI.Hierarchy.TaggedPassFormatCore
import OAI.Hierarchy.TaggedPassGeometry
import OAI.Hierarchy.TaggedRadixPrice

namespace OAI
/-! # The fixed integer schedule for all tagged radix passes -/

noncomputable section
namespace Hierarchy.Tagged.Radix

open Filter Real

def passesFor (a : ℝ) (h : ℕ) : ℕ := ⌈((h:ℝ)+1)/(digitBits a h:ℝ)⌉₊

def passShapeAt (a B : ℝ) (h n i : ℕ) : PassShape where
  digitBits := digitBits a h
  packBits := packBits B h
  rows := slotSequence (2^(h+1)) (digitBits a h) (packBits B h) (min i n)

def PassShape.format (s : PassShape) (w : ℕ) : PassFormat where
  first := 2*s.digitBits+1
  second := 2*s.digitBits+1
  wide := s.globalHeight
  copies := s.blocks
  firstW := 2*s.digitBits+1+w
  secondW := w
  wideW := s.globalHeight+s.pack*w

def passFormatAt (a B : ℝ) (h n i w : ℕ) : PassFormat := (passShapeAt a B h n i).format w

theorem GridScales.passesFor_bounds {a B : ℝ} {h : ℕ} (g : GridScales a B h) (ha : 1≤a) :
    0 < passesFor a h ∧ passesFor a h ≤ 2^(passBits h) ∧
    h+1 ≤ passesFor a h*digitBits a h ∧ (passesFor a h:ℝ) ≤ 6*(h:ℝ)^(1-1/a) := by
  have digits := g.digit_room
  have kp : 0 < digitBits a h := by omega
  have kpos : (0:ℝ) < digitBits a h := by exact_mod_cast kp
  have k1 : (1:ℝ) ≤ digitBits a h := by exact_mod_cast kp
  have h1 : (1:ℝ) ≤ h := by exact_mod_cast g.positive
  let p := passesFor a h
  have row : ((h:ℝ)+1)/(digitBits a h:ℝ) ≤ p := Nat.le_ceil _
  have range : p ≤ h+1 := by
    apply Nat.ceil_le.mpr
    push_cast
    exact div_le_self (by positivity) k1
  have fit : h+1 ≤ p*digitBits a h := by exact_mod_cast (div_le_iff₀ kpos).mp row
  have half : (h:ℝ)/(digitBits a h:ℝ)+1 ≤ 3*(h:ℝ)^(1-1/a) :=
    pass_count_factor h1 ha g.digit_lo le_rfl
  have raw := Nat.ceil_lt_add_one (div_nonneg (show 0 ≤ (h:ℝ)+1 by positivity) kpos.le)
  have dbl : ((h:ℝ)+1)/(digitBits a h:ℝ) ≤ 2*((h:ℝ)/(digitBits a h:ℝ)) := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by linarith) kpos.le
  refine ⟨Nat.ceil_pos.mpr (by positivity),range.trans g.passes,fit,?_⟩
  change (p:ℝ) ≤ _
  change (p:ℝ) < _ at raw
  linarith only [raw,dbl,half]

/-- At every pass the local batch and the wide padded call meet the actual
height, volume and payload hypotheses of the pricing theorem. -/
theorem GridScales.format_bounds {a B : ℝ} {h n c w : ℕ} (g : GridScales a B h)
    (two : 2 ≤ h) (count : n+1 ≤ 2^(passBits h)) (hw : 0<w) (width : w ≤ c*h) (i : ℕ) :
    FormatBounds a B h 2 (c+2) 8 (passFormatAt a B h n i w) := by
  let s := passShapeAt a B h n i
  have digits := g.digit_room
  have last := g.last_room
  have endRoom : passBits h+2*digitBits a h+2 ≤ h+1 := by omega
  have before := slotSequence_bounds count digits endRoom (min i n) (by omega)
  have after := slotSequence_bounds count digits endRoom (min i n+1) (by omega)
  change 2^(h+1) ≤ s.rows ∧ s.rows ≤ 2*2^(h+1) at before
  change 2^(h+1) ≤ s.nextRows ∧ s.nextRows ≤ 2*2^(h+1) at after
  rw [pow_succ] at before after
  have lie : s.packBits ≤ 2*s.digitBits := by
    change packBits B h ≤ 2*digitBits a h
    omega
  have je : s.packBits ≤ h := by change packBits B h ≤ h; omega
  have gu := s.global_height (h:=h) lie je (by omega) (by omega)
  have tagLen : 2*s.digitBits+1 ≤ h := by change 2*digitBits a h+1 ≤ h; omega
  have far : s.globalHeight ≤ 2*h := by omega
  have localLo : 2^h ≤ s.blocks*2^(2*s.digitBits+1) := by
    have inner := s.real_fit
    change s.rows ≤ s.blocks*2^(2*s.digitBits) at inner
    rw [pow_succ,← Nat.mul_assoc]
    omega
  have localHi := s.local_volume.trans (Nat.mul_le_mul_left 2 after.2)
  have localCap : s.blocks*2^(2*s.digitBits+1) ≤ 8*2^h := by omega
  have blocks : 0 < s.blocks := by
    by_contra! zero
    have eq : s.blocks = 0 := by omega
    rw [eq,Nat.zero_mul] at localLo
    exact (Nat.two_pow_pos h).not_ge localLo
  have firstW : 2*s.digitBits+1+w ≤ (c+2)*h := by rw [Nat.add_mul]; omega
  have secondW : w ≤ (c+2)*h := by rw [Nat.add_mul]; omega
  have base : h ≤ h*s.pack := Nat.le_mul_of_pos_right h (Nat.two_pow_pos _)
  have packed : s.pack*w ≤ c*h*s.pack :=
    (Nat.mul_le_mul_left s.pack width).trans_eq (Nat.mul_comm _ _)
  have wideW : s.globalHeight+s.pack*w ≤ (c+2)*h*s.pack := calc
    _ ≤ c*h*s.pack+2*(h*s.pack) := by omega
    _ = _ := by ring
  have pp : 0 < s.pack*w := Nat.mul_pos (Nat.two_pow_pos _) hw
  exact ⟨by dsimp [passFormatAt,PassShape.format,passShapeAt]; omega,
    by dsimp [passFormatAt,PassShape.format,passShapeAt]; omega,
    by dsimp [passFormatAt,PassShape.format,passShapeAt]; omega,
    by dsimp [passFormatAt,PassShape.format,passShapeAt]; omega,
    gu.1,gu.2,blocks,localLo,localCap,localLo,localCap,
    ⟨by change 0<2*s.digitBits+1+w; omega,firstW⟩,⟨hw,secondW⟩,
    ⟨by change 0<s.globalHeight+s.pack*w; omega,wideW⟩⟩

/-- The explicit seed is the paired input of 2^(h+1) rows. The last index
gives exactly the ceiling number of passes and covers all h+1 key bits. -/
theorem eventual_formats {a B : ℝ} (ha : 1<a) (hB : 1<B) :
    ∀ᶠ h : ℕ in atTop, ∃ n : ℕ, n+1 = passesFor a h ∧
      h+1 ≤ (n+1)*digitBits a h ∧ ((n+1:ℕ):ℝ) ≤ 6*(h:ℝ)^(1-1/a) ∧
      ∀ c w : ℕ, 0<w → w ≤ c*h → ∀ i : ℕ,
        FormatBounds a B h 2 (c+2) 8 (passFormatAt a B h n i w) := by
  filter_upwards [eventual_grid_scales ha hB,eventually_ge_atTop (2:ℕ)] with h grids two
  obtain ⟨pos,cap,key,price⟩ := grids.passesFor_bounds ha.le
  let n := passesFor a h - 1
  have eq : n+1 = passesFor a h := by dsimp [n]; omega
  refine ⟨n,eq,by simpa only [eq] using key,by simpa only [eq] using price,?_⟩
  intro c w hw room i
  exact grids.format_bounds two (by simpa only [eq] using cap) hw room i

theorem eventual_start_formats {a B : ℝ} (ha : 1<a) (hB : 1<B) :
    ∀ᶠ h : ℕ in atTop, ∃ n : ℕ, n+1 = passesFor a h ∧
      h+1 ≤ (n+1)*digitBits a h ∧ ((n+1:ℕ):ℝ) ≤ 6*(h:ℝ)^(1-1/a) ∧
      ∀ i : ℕ, FormatBounds a B h 2 6 8 (passFormatAt a B h n i (2*h+4)) := by
  filter_upwards [eventual_formats ha hB,eventually_ge_atTop (2:ℕ)] with h formats two
  obtain ⟨n,eq,key,price,ready⟩ := formats
  exact ⟨n,eq,key,price,ready 4 (2*h+4) (by omega) (by omega)⟩

end Hierarchy.Tagged.Radix

end
end OAI
