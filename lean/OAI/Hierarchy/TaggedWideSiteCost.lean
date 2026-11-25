import OAI.Hierarchy.TaggedGapScale

namespace OAI
/-! # Cost of all fixed finite signed site templates on the native calendar -/

noncomputable section
namespace Hierarchy.Tagged
open Filter Real
open scoped BigOperators

/-- The stable compactor's binary address length on a true paid site
aperture grows at most logarithmically in the parent height. -/
theorem site_log (A : ℝ) (P : ℕ) (hP : 1≤P) (h w v : ℕ)
    (hi : 1≤log (h:ℝ)) (hh : 0<h) (hw : 0<w) (width : (w:ℝ)≤(h:ℝ)^A)
    (positive : 0<v) (room : v≤P*w) :
    (Nat.log 2 v:ℝ)+2 ≤ (logb 2 (P:ℝ)+2+A/log 2)*log (h:ℝ) := by
  have hp : (1:ℝ)≤P := by exact_mod_cast hP
  have hp0 : 0<(P:ℝ) := zero_lt_one.trans_le hp
  have hw0 : 0<(w:ℝ) := Nat.cast_pos.mpr hw
  have large : (v:ℝ)≤(P:ℝ)*w := by exact_mod_cast room
  have corr := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) (Nat.cast_pos.mpr positive) large
  rw [Real.logb_mul hp0.ne' hw0.ne'] at corr
  have wr := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) hw0 width
  rw [Real.logb_rpow_eq_mul_logb_of_pos (Nat.cast_pos.mpr hh)] at wr
  have sol := Real.natLog_le_logb v 2
  have logP := Real.logb_nonneg (by norm_num : (1:ℝ)<2) hp
  have cpos : 0≤logb 2 (P:ℝ)+2 := by linarith
  have agree : A*logb 2 (h:ℝ)=(A/log 2)*log (h:ℝ) := by unfold Real.logb;ring
  rw [agree] at wr
  norm_num only [Nat.cast_ofNat] at sol
  nlinarith [mul_nonneg cpos (sub_nonneg.mpr hi)]

/-- Sum the actual per-site LUT and stable-compactor bill (`Packet.site_cost`).
Bounds on the public template dimensions are fixed by the finite protocol
menu; the multiplicity may vary over all paid physical rows. -/
theorem eventually_site_bill (A : ℝ) (J d e flat B : ℕ) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ h : ℕ in atTop,∀ {w rows : ℕ},0<w → (w:ℝ)≤(h:ℝ)^A →
      rows≤B*2^h → ∀ (copies fee : Fin rows→ℕ), (∀ i,copies i≤J*w) →
      (∀ i,fee i≤copies i*flat+2*(e*(copies i*d))+
        128000*e*(copies i*d+1)*(Nat.log 2 (copies i*d+1)+2)^3) →
      ((∑i,fee i:ℕ):ℝ) ≤ C*((2:ℝ)^h*w*(log (h:ℝ))^3) := by
  let P := J*d+1
  let L := max 1 (logb 2 (P:ℝ)+2+A/log 2)
  let c : ℝ := J*flat+2*(e*(J*d:ℕ):ℕ)+128000*(e:ℝ)*P*L^3
  have hP : 1≤P := by dsimp [P]; omega
  have lpos : 0≤L := (by norm_num : (0:ℝ)≤1).trans (le_max_left ..)
  have cpos : 0≤c := by dsimp [c]; positivity
  refine ⟨(B:ℝ)*c+1,by positivity,?_⟩
  filter_upwards [(Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 1,
    eventually_ge_atTop (1:ℕ)] with h high hh
  change 1≤log (h:ℝ) at high
  intro w rows hw width count copies fee bound cost
  have cube : 1≤(log (h:ℝ))^3 := one_le_pow₀ high
  have hlog : 0≤log (h:ℝ) := by linarith
  have per (i : Fin rows) : (fee i:ℝ)≤c*(w:ℝ)*(log (h:ℝ))^3 := by
    let r := copies i
    have size : r*d+1≤P*w := by
      have times := Nat.mul_le_mul_right d (bound i)
      dsimp [P]
      rw [Nat.add_mul,Nat.one_mul]
      calc
        r*d+1 ≤ (J*w)*d+w := Nat.add_le_add times hw
        _ = _ := by ring
    have field := site_log A P hP h w (r*d+1) high hh hw width (by omega) size
    have logs : (Nat.log 2 (r*d+1):ℝ)+2≤L*log (h:ℝ) :=
      field.trans (mul_le_mul_of_nonneg_right (le_max_right ..) (by linarith))
    have upper : (r:ℝ)≤(J:ℝ)*w := by exact_mod_cast bound i
    have aperture : ((r*d+1:ℕ):ℝ)≤(P:ℝ)*w := by exact_mod_cast size
    have comp : ((Nat.log 2 (r*d+1)+2:ℕ):ℝ)^3≤(L*log (h:ℝ))^3 := by
      apply pow_le_pow_left₀ (by positivity)
      simpa using logs
    have crude : (fee i:ℝ) ≤ (r:ℝ)*flat+2*((e:ℝ)*(r*d))+
        128000*e*((r*d+1:ℕ):ℝ)*(((Nat.log 2 (r*d+1)+2:ℕ):ℝ)^3) := by exact_mod_cast cost i
    calc
      _ ≤ _ := crude
      _ ≤ (J*w:ℕ)*flat+2*(e*((J*w:ℕ)*d):ℕ)+
          (128000:ℝ)*e*((P:ℝ)*w)*(L*log (h:ℝ))^3 := by
        push_cast at aperture ⊢
        gcongr
      _ ≤ _ := by
        dsimp [c]
        push_cast
        have main : 0≤(J:ℝ)*w*flat+2*(e*((J:ℝ)*w*d)) := by positivity
        nlinarith only [mul_nonneg main (sub_nonneg.mpr cube)]
  have total := Finset.sum_le_sum (s:=Finset.univ) (fun i _=>per i)
  have num : (rows:ℝ)≤(B:ℝ)*(2:ℝ)^h := by exact_mod_cast count
  calc
    _ ≤ (rows:ℝ)*(c*(w:ℝ)*(log (h:ℝ))^3) := by simpa [Nat.cast_sum,Finset.sum_const,nsmul_eq_mul] using total
    _ ≤ ((B:ℝ)*(2:ℝ)^h)*(c*w*(log (h:ℝ))^3) := mul_le_mul_of_nonneg_right num (by positivity)
    _ ≤ _ := by nlinarith only [show 0≤(2:ℝ)^h*w*(log (h:ℝ))^3 by positivity]

end Hierarchy.Tagged

end
end OAI
