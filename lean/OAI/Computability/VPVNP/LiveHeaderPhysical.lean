import OAI.Computability.VPVNP.LiveHeaderShapes

/-!
# Typed cut fields at their physical processor sites

The descriptor arithmetic addresses the same bits as the paper's typed
cut layout. In particular the exponent vector uses label-major order,
with the least significant bit first inside each label word.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeaderDescriptors.Physical

open CutSchedule

section Pair

variable {h Δ i t Z : ℕ} (hi : 0 < i) (hle : i ≤ 2^h) (hfit : 1+t*Z ≤ Δ)
variable (bits : Bits (width (h+1) Δ i))

theorem pair_mode (site : Fin (width (h+1) Δ i)) (hs : site.val = 0) :
    (firstHalfLayout h Δ i t Z hi hle hfit bits).1 = bits site := by
  change bits _ = bits site
  apply congrArg bits
  exact Fin.ext hs.symm

private theorem pair_starts (f : Field) (j : ℕ) (hj : j < count .pair (width (h+1) Δ i) Δ (t*Z) 0 f) :
    (span .pair (width (h+1) Δ i) Δ (t*Z) 0 f).1 = start .pair (width (h+1) Δ i) Δ (t*Z) 0 f := by
  simp [span, show count .pair (width (h+1) Δ i) Δ (t*Z) 0 f ≠ 0 by omega]

theorem pair_exterior (j : Fin (width (h+1) Δ (2*i))) (site : Fin (width (h+1) Δ i))
    (hs : site.val = (span .pair (width (h+1) Δ i) Δ (t*Z) 0 .exterior).1 + j.val) :
    (firstHalfLayout h Δ i t Z hi hle hfit bits).2.1 j = bits site := by
  have hlen := LiveHeaderDescriptors.pair_exterior h Δ i hi hle
  have hmode : mode (width (h+1) Δ i) = 1 := by
    rw [mode, width_double h Δ i hi hle, ite_eq_right (by omega)]
  have hj : j.val < count .pair (width (h+1) Δ i) Δ (t*Z) 0 .exterior := by
    change j.val < exterior .pair (width (h+1) Δ i) Δ
    rw [hlen]; exact j.isLt
  rw [pair_starts .exterior j.val hj, start, hmode] at hs
  change bits _ = bits site
  apply congrArg bits
  exact Fin.ext hs.symm

private theorem pair_exp_bits (a : Fin t) (b : Fin Z) :
    let q := firstHalfLayout h Δ i t Z hi hle hfit bits
    RAMSerialization.wordBits Z (q.2.2.1 a) b =
      RAMSerialization.arrayBits t Z q.2.2.1 (finProdFinEquiv (a,b)) :=
  (RAMSerialization.arrayBits_at _ a b).symm

theorem pair_exponent (a : Fin t) (b : Fin Z) (site : Fin (width (h+1) Δ i))
    (hs : site.val = (span .pair (width (h+1) Δ i) Δ (t*Z) 0 .exponents).1 + a.val*Z + b.val) :
    RAMSerialization.wordBits Z ((firstHalfLayout h Δ i t Z hi hle hfit bits).2.2.1 a) b = bits site := by
  let j := finProdFinEquiv (a,b)
  have hj : j.val < count .pair (width (h+1) Δ i) Δ (t*Z) 0 .exponents := j.isLt
  have hlen := LiveHeaderDescriptors.pair_exterior h Δ i hi hle
  have hmode : mode (width (h+1) Δ i) = 1 := by
    rw [mode, width_double h Δ i hi hle, ite_eq_right (by omega)]
  rw [pair_starts .exponents j.val hj, start, hmode, hlen] at hs
  rw [pair_exp_bits hi hle hfit bits a b]
  change RAMSerialization.arrayBits t Z ((RAMSerialization.arrayBits t Z).symm _) j = _
  rw [Equiv.apply_symm_apply]
  change bits _ = bits site
  apply congrArg bits
  apply Fin.ext
  change 1+(width (h+1) Δ (2*i)+(b.val+Z*a.val)) = site.val
  rw [Nat.mul_comm Z a.val]
  omega

theorem pair_padding (j : Fin (Δ-(1+t*Z))) (site : Fin (width (h+1) Δ i))
    (hs : site.val = (span .pair (width (h+1) Δ i) Δ (t*Z) 0 .padding).1 + j.val) :
    (firstHalfLayout h Δ i t Z hi hle hfit bits).2.2.2 j = bits site := by
  have hlen := LiveHeaderDescriptors.pair_exterior h Δ i hi hle
  have hw := width_double h Δ i hi hle
  have hmode : mode (width (h+1) Δ i) = 1 := by rw [mode, hw, ite_eq_right (by omega)]
  have hstart : start .pair (width (h+1) Δ i) Δ (t*Z) 0 .padding = 1+width (h+1) Δ (2*i)+t*Z := by
    simp [start,hmode,hlen,exponents,config]
  have hj : j.val < count .pair (width (h+1) Δ i) Δ (t*Z) 0 .padding := by
    rw [count, hstart, hw]
    have := j.isLt
    omega
  rw [pair_starts .padding j.val hj, hstart] at hs
  change bits _ = bits site
  apply congrArg bits
  apply Fin.ext
  change 1+(width (h+1) Δ (2*i)+(t*Z+j.val)) = site.val
  omega

end Pair

section Tail

variable {h Δ i c : ℕ} (hhalf : 2^h ≤ i) (hend : i < 2^(h+1)) (hfit : 1+c ≤ Δ)
variable (bits : Bits (width (h+1) Δ i))

theorem tail_mode (site : Fin (width (h+1) Δ i)) (hs : site.val = 0) :
    (tailLayout h Δ i c hhalf hend hfit bits).1 = bits site := by
  change bits _ = bits site
  apply congrArg bits
  exact Fin.ext hs.symm

theorem tail_config (j : Fin c) (site : Fin (width (h+1) Δ i))
    (hs : site.val = (span .tail (width (h+1) Δ i) Δ 0 c .config).1 + j.val) :
    (tailLayout h Δ i c hhalf hend hfit bits).2.1 j = bits site := by
  have hc : c ≠ 0 := fun he => by have := j.isLt; omega
  have hΔ : Δ ≠ 0 := by omega
  simp [span, count, start, mode, exterior, exponents, config, width_tail h Δ i hhalf hend, hc, hΔ] at hs
  change bits _ = bits site
  apply congrArg bits
  exact Fin.ext hs.symm

theorem tail_padding (j : Fin (Δ-(1+c))) (site : Fin (width (h+1) Δ i))
    (hs : site.val = (span .tail (width (h+1) Δ i) Δ 0 c .padding).1 + j.val) :
    (tailLayout h Δ i c hhalf hend hfit bits).2.2 j = bits site := by
  have hΔ : Δ ≠ 0 := by omega
  have hp : Δ-(1+c) ≠ 0 := fun he => by have := j.isLt; omega
  simp [span, count, start, mode, exterior, exponents, config, width_tail h Δ i hhalf hend, hp, hΔ] at hs
  change bits _ = bits site
  apply congrArg bits
  apply Fin.ext
  change 1+(c+j.val) = site.val
  omega

end Tail
/-- The field runner tests exactly these bits for zero. -/
def ZeroSlice {W : ℕ} (bits : Bits W) (iv : ℕ × ℕ) : Prop :=
  ∀ (j : ℕ) (site : Fin W), j < iv.2 → site.val = iv.1 + j → bits site = false

private theorem decoded_zero {W n : ℕ} (bits : Bits W) (iv : ℕ × ℕ) (field : Fin n → Bool)
    (hlen : iv.2 = n) (hfit : iv.1 + iv.2 ≤ W)
    (hphys : ∀ (j : Fin n) (site : Fin W), site.val = iv.1+j.val → field j = bits site) :
    ZeroSlice bits iv ↔ field = fun _ => false := by
  constructor
  · intro hz
    funext j
    have hj := j.isLt
    let site : Fin W := ⟨iv.1+j.val,by omega⟩
    rw [hphys j site rfl]
    exact hz j.val site (by omega) rfl
  · intro h j site hj hs
    let k : Fin n := ⟨j,by omega⟩
    rw [← hphys k site hs, h]

/-- Unit mode accepts exactly the all-zero cut once its mode bit is checked. -/
theorem unit_zero_iff {W : ℕ} (bits : Bits W) (Δ e c : ℕ) :
    ((∀ site : Fin W, site.val = 0 → bits site = false) ∧
      ZeroSlice bits (span .unit W Δ e c .padding)) ↔ ∀ site, bits site = false := by
  constructor
  · rintro ⟨hm,hz⟩ site
    by_cases h0 : site.val = 0
    · exact hm site h0
    · have h := site.isLt
      have hW : W ≠ 0 := by omega
      have hpad : W-1 ≠ 0 := by omega
      have hiv : span .unit W Δ e c .padding = (1,W-1) := by
        simp [span,count,start,mode,exterior,exponents,config,hW,hpad]
      rw [hiv] at hz
      exact hz (site.val-1) site (by change _ < W-1; omega) (by change site.val = 1+_; omega)
  · intro h
    exact ⟨fun site _ => h site, fun _ site _ _ => h site⟩

/-- The physical padding guard on a first-half cut is exactly the zero
padding constraint in the typed path equivalence. -/
theorem pair_padding_zero {h Δ i t Z : ℕ} (hi : 0 < i) (hle : i ≤ 2^h) (hfit : 1+t*Z ≤ Δ)
    (bits : Bits (width (h+1) Δ i)) :
    ZeroSlice bits (span .pair (width (h+1) Δ i) Δ (t*Z) 0 .padding) ↔
      (firstHalfLayout h Δ i t Z hi hle hfit bits).2.2.2 = fun _ => false := by
  have hw := width_double h Δ i hi hle
  have hlen := LiveHeaderDescriptors.pair_exterior h Δ i hi hle
  have hmode : mode (width (h+1) Δ i) = 1 := by rw [mode, hw, ite_eq_right (by omega)]
  apply decoded_zero
  · change width (h+1) Δ i - start .pair (width (h+1) Δ i) Δ (t*Z) 0 .padding = Δ-(1+t*Z)
    simp [start, hmode, hlen, exponents, config]
    omega
  · exact span_fit hfit (by omega) (fun _ => by omega) .padding
  · exact pair_padding hi hle hfit bits

theorem tail_padding_zero {h Δ i c : ℕ} (hhalf : 2^h ≤ i) (hend : i < 2^(h+1))
    (hfit : 1+c ≤ Δ) (bits : Bits (width (h+1) Δ i)) :
    ZeroSlice bits (span .tail (width (h+1) Δ i) Δ 0 c .padding) ↔
      (tailLayout h Δ i c hhalf hend hfit bits).2.2 = fun _ => false := by
  have hw := width_tail h Δ i hhalf hend
  apply decoded_zero
  · simp [span, count, start, mode, exterior, exponents, config, hw, show Δ ≠ 0 by omega]
  · exact span_fit (by omega) hfit (fun _ => hw.ge) .padding
  · exact tail_padding hhalf hend hfit bits

end LiveHeaderDescriptors.Physical

end VPVNP
end Computability
end OAI
