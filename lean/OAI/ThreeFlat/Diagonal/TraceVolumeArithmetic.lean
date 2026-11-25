import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import OAI.ThreeFlat.Diagonal.DefectBudget

namespace OAI
/-! # The time and space reserved for the diagonal tick template -/

namespace ThreeFlat.Diagonal.TraceVolume

/-- The exponent is chosen independently of the eventual evaluator. -/
def cm := 300

def cap (u : ℕ) := 2^(u^10)/u^cm

def depth (u : ℕ) := (cap u).log2

theorem cap_pos {u : ℕ} (hu : cm ≤ u) : 0 < cap u := by
  have hp : 0 < u := by simp [cm] at hu; omega
  exact Nat.div_pos ((width_pow_le_two_pow_sq hu).trans (Nat.pow_le_pow_right (by decide)
    (Nat.pow_le_pow_right hp (by decide : 2 ≤ 10)))) (Nat.pow_pos hp)

/-- Round the time cap down to a power of two with loss smaller than two. -/
theorem sites_cap {u : ℕ} (hu : cm ≤ u) :
    2^(depth u) ≤ cap u ∧ cap u < 2*2^(depth u) := by
  have h := (Nat.log2_eq_iff (Nat.ne_of_gt (cap_pos hu))).mp (show (cap u).log2 = depth u from rfl)
  exact ⟨h.1,by simpa only [pow_succ,Nat.mul_comm _ 2] using h.2⟩

theorem depth_le (u : ℕ) : depth u ≤ u^10 := by
  by_cases h : cap u = 0
  · simp [depth,h]
  · apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    exact (Nat.log2_self_le h).trans (Nat.div_le_self _ _)

/-- Rounding the polynomially shortened time cap preserves the leading
u¹⁰ term of its logarithm. -/
theorem depth_lower {u : ℕ} (hu : cm ≤ u) : u^10-u^2 ≤ depth u := by
  have hp : 0<u := by dsimp [cm] at hu; omega
  have powers : u^2 ≤ u^10 := Nat.pow_le_pow_right hp (by decide)
  apply (Nat.le_log2 (Nat.ne_of_gt (cap_pos hu))).mpr
  apply (Nat.le_div_iff_mul_le (Nat.pow_pos hp)).mpr
  calc
    _ ≤ 2^(u^10-u^2)*2^(u^2) := Nat.mul_le_mul_left _ (width_pow_le_two_pow_sq hu)
    _ = _ := by rw [← Nat.pow_add,Nat.sub_add_cancel powers]

theorem sites_mul {u : ℕ} (hu : cm ≤ u) : 2^(depth u)*u^cm ≤ 2^(u^10) :=
  (Nat.mul_le_mul_right _ (sites_cap hu).1).trans (Nat.div_mul_le_self _ _)

/-- Raw cells and bits, filling the local public tables once, and one
descriptor execution per emitted word of every trivalent cell. -/
def graphVolume (cells hidden pins : ℕ) := 10*(cells+hidden+pins+1)

def linkingTime (cells hidden pins : ℕ) := 9+17*(2+pins+hidden)+78*cells

def work (sites S shared localHidden cells ports width binds : ℕ) :=
  S+shared+sites*localHidden+sites*cells +
    (11*(sites*cells))*(2*binds+4) + 11*(cells+ports)*(5*width+6) + 16 +
    graphVolume (sites*cells) (shared+sites*localHidden) S +
    linkingTime (sites*cells) (shared+sites*localHidden) S

/-- Both the constant public-table descriptor (≤430 binds) and the
literal-table descriptor (≤33 cells+42 ports+122) fit this allowance. -/
def bindAllowance (cells ports : ℕ) := 430+33*cells+42*ports+122

private def localWork (cells ports width : ℕ) :=
  125+28*ports+117*cells + 11*cells*(2*bindAllowance cells ports+4) +
    11*(cells+ports)*(5*width+6)

private theorem work_le {sites S shared localHidden cells ports width binds : ℕ} (hsite : 1 ≤ sites)
    (hs : S ≤ 2*sites) (hm : shared ≤ sites*ports) (hh : localHidden ≤ cells)
    (hb : binds ≤ bindAllowance cells ports) :
    work sites S shared localHidden cells ports width binds ≤ sites*localWork cells ports width := by
  have ht : 11*(cells+ports)*(5*width+6) ≤ sites*(11*(cells+ports)*(5*width+6)) :=
    Nat.le_mul_of_pos_left _ hsite
  have overhead : 69 ≤ sites*69 := Nat.le_mul_of_pos_left _ hsite
  calc
    _ = (28*S+28*shared+28*(sites*localHidden)+89*(sites*cells)) +
        (11*(sites*cells))*(2*binds+4) + 11*(cells+ports)*(5*width+6)+69 := by
      unfold work graphVolume linkingTime; ring
    _ ≤ (28*(2*sites)+28*(sites*ports)+28*(sites*cells)+89*(sites*cells)) +
        (11*(sites*cells))*(2*bindAllowance cells ports+4) +
        sites*(11*(cells+ports)*(5*width+6)) + sites*69 := by gcongr
    _ = _ := by unfold localWork; ring

theorem graphVolume_le_work (sites S shared localHidden cells ports width binds : ℕ) :
    graphVolume (sites*cells) (shared+sites*localHidden) S ≤
    work sites S shared localHidden cells ports width binds := by unfold work; omega

theorem linkingTime_le_work (sites S shared localHidden cells ports width binds : ℕ) :
    linkingTime (sites*cells) (shared+sites*localHidden) S ≤
    work sites S shared localHidden cells ports width binds := by unfold work; omega

set_option exponentiation.threshold 283 in
private theorem localWork_le {u cells ports width : ℕ} (hu : 50000 ≤ u)
    (hc : cells ≤ u^141) (hp : ports ≤ u^141) (hw : width ≤ u^141) :
    localWork cells ports width ≤ u^cm := by
  let x := u^141
  have hx : 1 ≤ x := Nat.one_le_pow _ _ (by omega)
  have hxx : x ≤ x*x := Nat.le_mul_of_pos_right _ hx
  calc
    _ ≤ localWork x x x := by unfold localWork bindAllowance; gcongr
    _ ≤ 50000*(x*x) := by
      unfold localWork bindAllowance
      ring_nf at hxx ⊢
      omega
    _ ≤ u*(x*x) := Nat.mul_le_mul_right _ hu
    _ = u^283 := by dsimp [x]; ring
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide : 283 ≤ cm)

theorem work_le_volume {u S shared localHidden cells ports binds : ℕ} (hu : 50000 ≤ u)
    (hc : cells ≤ u^141) (hp : ports ≤ u^141)
    (hs : S ≤ 2*2^(depth u)) (hm : shared ≤ 2^(depth u)*ports) (hh : localHidden ≤ cells)
    (hb : binds ≤ bindAllowance cells ports) :
    work (2^(depth u)) S shared localHidden cells ports (16*u^10) binds ≤ 2^(u^10) := by
  have hw : 16*u^10 ≤ u^141 := calc
    _ ≤ u*u^10 := Nat.mul_le_mul_right _ (by omega)
    _ = u^11 := by ring
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide)
  have hcm : cm ≤ u := by simp [cm]; omega
  exact (work_le (Nat.two_pow_pos _) hs hm hh hb).trans
    ((Nat.mul_le_mul_left _ (localWork_le hu hc hp hw)).trans (sites_mul hcm))

end ThreeFlat.Diagonal.TraceVolume

end OAI
