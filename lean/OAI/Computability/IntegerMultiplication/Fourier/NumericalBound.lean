import OAI.Computability.IntegerMultiplication.Fourier.Recover

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Fourier

/- Coarse exponent accounting for the three errors in line_est. -/

private theorem expo_merge (u v : ℝ) : Real.exp u*Real.exp v=Real.exp (u+v) :=
  (Real.exp_add u v).symm

theorem combine_errors
    (H P C t s q qpow cut tail : ℝ)
    (hP : 4≤P) (hH : 0≤H)
    (_hc' : 0≤C) (hs' : 0≤s) (ht' : 0≤t) (_hq' : 0≤q)
    (hqpow' : 0≤qpow) (hcut' : 0≤cut) (_htail' : 0≤tail)
    (hc : C≤Real.exp (4*P)) (ht : t≤Real.exp P) (hs : s≤Real.exp P) (hq : q≤1/2)
    (hqpow : qpow ≤ Real.exp (-(H+12)*P)) (hcut : cut≤Real.exp (-(H+12)*P))
    (htail : tail ≤ Real.exp (-(H+12)*P)) :
    2*(C*(t*(s*cut)))+qpow*((q+tail)*s)+2*(tail*s) ≤ Real.exp (-H*P) := by
  have hp : 0≤P := by linarith
  have htail₁ : tail ≤ 1 := htail.trans (Real.exp_le_one_iff.mpr (by nlinarith))
  let Z := Real.exp (-(H+1)*P)
  have h₁ : C*(t*(s*cut)) ≤ Z := by
    calc
      _ ≤ Real.exp (4*P)*(Real.exp P*(Real.exp P*Real.exp (-(H+12)*P))) := by gcongr
      _ ≤ Z := by simp only [expo_merge]; apply Real.exp_le_exp.mpr; nlinarith
  have h₂ : qpow*s ≤ Z :=
    calc
      _ ≤ Real.exp (-(H+12)*P)*Real.exp P := by gcongr
      _ ≤ Z := by simp only [expo_merge]; apply Real.exp_le_exp.mpr; nlinarith
  have h₃ : tail*s ≤ Z :=
    calc
      _ ≤ Real.exp (-(H+12)*P)*Real.exp P := by gcongr
      _ ≤ Z := by simp only [expo_merge]; apply Real.exp_le_exp.mpr; nlinarith
  have h₂' : qpow*((q+tail)*s) ≤ 2*Z := by
    rw [show qpow*((q+tail)*s)=(q+tail)*(qpow*s) by ring]
    have := mul_le_mul_of_nonneg_right (show q+tail≤2 by linarith) (mul_nonneg hqpow' hs')
    linarith
  have hh : 6≤Real.exp P := by
    have h := Real.add_one_le_exp (P/2)
    rw [show P=P/2+P/2 by ring,Real.exp_add] -- rewrites within? kinds
    nlinarith
  have ee : Real.exp P*Z=Real.exp (-H*P) := by rw [expo_merge]; congr 1; ring
  rw [← ee]
  have : 0 ≤ Z := (Real.exp_pos _).le
  nlinarith

/- Parameter choices work for all sufficiently large integer dimensions d.
No special arithmetic assumptions on s,t. -/

def paramPrec (d : ℕ) := d^32
def paramR (d : ℕ) := d^16
def paramJ (d : ℕ) := d^9
def paramK (d : ℕ) := d^18 -- Neumann k; DIFFERENT K from chunk width
def paramL (d : ℕ) := d^26
def paramD (d s : ℕ) := s^2 / paramR d

-- record natural-rank facts
theorem paramD_spec {d s : ℕ} (h : 2 ≤ d) (hs : paramPrec d ≤ s) :
    let D := paramD d s
    let R := paramR d
    R*D ≤ s^2 ∧ s^2 ≤ 2*R*D ∧ 4*s≤D := by
  let D := paramD d s
  let R := paramR d
  change R*D ≤ _ ∧ _ ≤ 2*R*D ∧ _≤D
  have hr : 0<R := pow_pos (by omega) _
  have h₁ : R*D ≤ s^2 := by
    rw [mul_comm]
    apply Nat.div_mul_le_self
  have hh : 4*R ≤ s := by
    have hP : 4 ≤ d^16 :=
      calc
        _ ≤ d^2 := by nlinarith
        _ ≤ d^16 := pow_le_pow_right₀ (by omega) (by norm_num)
    exact (show 4*d^16 ≤ d^32 by
      rw [show 32=16+16 from rfl,pow_add]
      exact Nat.mul_le_mul_right _ hP).trans hs
  have heq : s^2 < R*(D+1) := by
    have hm := Nat.mod_add_div (s^2) R
    change _ + R * D = _ at hm
    have hu := Nat.mod_lt (s^2) hr
    rw [Nat.mul_add, mul_one]
    omega
  have hq : 4*s≤D := by
    unfold D paramD
    apply (Nat.le_div_iff_mul_le hr).mpr
    nlinarith
  refine ⟨h₁,?_,hq⟩
  have hp := Nat.mul_le_mul_left R (show D+1≤ D+D by omega)
  nlinarith

private theorem huge {d : ℕ} {H : ℝ} (hd : 64*(H+20) ≤ (d:ℝ)) (hH : 0 ≤ H) :
    2 ≤ d := by
  by_contra! h
  exact absurd (show (d:ℝ) < 2 from by exact_mod_cast h) (by linarith)

/-- Symbolic coefficients in line_est for our parameter choices. Bounds are
deliberately coarse and use exp to compare exponents; H controls requested error.
-/
theorem param_est {d s t : ℕ} [NeZero s] [NeZero t] {H : ℝ}
    (hH : 0 ≤ H)
    (hd : 64*(H+20)≤ (d:ℝ))
    (hs : paramPrec d ≤ s) (ht : t ≤ 2^paramPrec d)
    (hg : ((1:ℝ)+1/(8*d))*(s:ℕ)≤(t:ℝ)) :
    let P : ℝ := (paramPrec d : ℕ)
    let J := paramJ d
    let K := paramK d
    let L := paramL d
    let R := paramR d
    let D := paramD d s
    let q := Real.exp (-(d:ℝ)^15/32)
    let r := Real.exp (-(H+12)*P)
    let C := (2*D+1)*Real.exp (R:ℝ)
    (∀ i : Spot s, ∑ j ∈ nhood J, ratio t D (delta s t i) j≤q) ∧
    (∀ i : Spot s, ∑ j ∈ nhood (2*D) \ nhood J, ratio t D (delta s t i) j≤r) ∧
    (∀ i : Spot s, 1/(coef D (delta s t i)) ≤ C) ∧
    0≤q ∧ q≤1/2 ∧ 0≤r ∧ 0≤C ∧ q^K ≤ r ∧
    Real.exp (-(4:ℝ)*D*L^2/s^2) ≤ r ∧
    C ≤ Real.exp (4*P) ∧ (s:ℝ)≤Real.exp P ∧ (t:ℝ)≤Real.exp P := by
  let P : ℝ := (paramPrec d : ℕ)
  let J := paramJ d
  let K := paramK d
  let L := paramL d
  let R := paramR d
  let D := paramD d s
  let q := Real.exp (-(d:ℝ)^15/32)
  let r := Real.exp (-(H+12)*P)
  let C := (2*(D:ℝ)+1)*Real.exp (R:ℝ)
  let X := (d:ℝ)
  change (∀ i : Spot s, ∑ j ∈ nhood J, ratio t D (delta s t i) j≤q) ∧
    (∀ i : Spot s, ∑ j ∈ nhood (2*D) \ nhood J, ratio t D (delta s t i) j≤r) ∧
    (∀ i : Spot s, 1/(coef D (delta s t i)) ≤ C) ∧
    0≤q ∧ q≤1/2 ∧ 0≤r ∧ 0≤C ∧ q^K ≤ r ∧
    Real.exp _ ≤ r ∧ C ≤ Real.exp (4*P) ∧ (s:ℝ)≤Real.exp P ∧ (t:ℝ)≤Real.exp P
  have hu := huge hd hH
  change 64*(H+20)≤X at hd
  have hx : 64≤X := by linarith
  have hx' : 1≤X := by linarith
  have hxpos : 0<X := by linarith
  have hD := paramD_spec hu hs
  change R*D ≤ _ ∧ _ ≤ 2*R*D ∧ 4*s≤D at hD
  have hsposN := Nat.pos_of_ne_zero (NeZero.ne s)
  have hspos : 0<(s:ℝ) := by exact_mod_cast hsposN
  have he : (s:ℝ)≤t := by
    have h : 0≤1/(8*X)*s := by positivity
    change (1+1/(8*X))*s ≤ (t:ℝ) at hg
    nlinarith
  have hmax : (t:ℝ) ≤ Real.exp P := by
    have h₁ : (t:ℝ) ≤ (2:ℝ)^paramPrec d := by exact_mod_cast ht
    have h₂ : 2≤Real.exp 1 := by linarith [Real.add_one_le_exp 1]
    apply h₁.trans
    calc
      _ ≤ Real.exp 1^paramPrec d := pow_le_pow_left₀ (by positivity) h₂ _
      _ = Real.exp P := by rw [← Real.exp_nat_mul]; simp [P]
  have hDs : (D:ℝ) ≤ (s:ℝ)^2 := by
    have h : D ≤ s^2 := Nat.div_le_self _ _
    exact_mod_cast h
  have hDexp : (D:ℝ) ≤ Real.exp (2*P) :=
    calc
      _ ≤ (s:ℝ)^2 := hDs
      _ ≤ Real.exp P ^ 2 := pow_le_pow_left₀ (by positivity) (he.trans hmax) 2
      _ = Real.exp (2*P) := by rw [two_mul, Real.exp_add]; ring
  have hz : (2*D+1:ℝ) ≤ Real.exp (3*P) ∧ (4*D+1:ℝ) ≤ Real.exp (3*P) := by
    have ep : P=X^32 := by dsimp [P,X,paramPrec]; push_cast; rfl
    have hl : 4≤P := by
      rw [ep]
      exact le_trans (by linarith : 4≤X) (le_self_pow₀ hx' (by norm_num))
    have hmax' : 1 ≤ Real.exp (2*P) := Real.one_le_exp_iff.mpr (by linarith)
    have hss : 5≤ Real.exp P := le_trans (by linarith : 5≤P+1) (Real.add_one_le_exp _)
    rw [show 3*P=2*P+P by ring, Real.exp_add]
    constructor <;> nlinarith only [mul_le_mul_of_nonneg_left hss (hmax'.trans' (by norm_num : (0:ℝ)≤1)), hDs, hmax', hDexp]
  have eR : (R:ℝ) = X^16 := by simp [paramR,R,X]
  have eP : P=X^32 := by simp [paramPrec,P,X]
  have eJ : (J:ℝ)=X^9 := by simp [paramJ,J,X]
  have eL : (L:ℝ)=X^26 := by simp [paramL,L,X]
  have eK : (K:ℝ)=X^18 := by simp [paramK,K,X]
  have ha (i : Spot s) : 4*|delta s t i| ≤ (D:ℤ) ∧ |((delta s t i : ℤ):ℝ)| ≤ (s:ℝ)/2 := by
    have hh := delta_small s t i
    have hw : 4 * (s:ℤ) ≤ D := by exact_mod_cast hD.2.2
    have e : 2*|(delta s t i:ℝ)| ≤ (s:ℝ) := by exact_mod_cast hh
    constructor <;> linarith
  have hz' i : delta s t i∈rad D := Finset.mem_Icc.mpr --? unfolds
    (abs_le.mp (show |delta s t i| ≤ (D:ℤ) by linarith [(ha i).1, abs_nonneg (delta s t i)]))
  have hWD : (R:ℝ)*D ≤ (s:ℝ)^2 := by exact_mod_cast hD.1
  have hWD' : (s:ℝ)^2 ≤ 2*(R:ℝ)*D := by exact_mod_cast hD.2.1
  have hn : 0<D := by omega
  have hbig : 1≤8*X := by linarith
  have hX15 : 64^2 ≤ X^15 :=
    calc
      _ ≤ X^2 := pow_le_pow_left₀ (by positivity) hx 2
      _ ≤ X^15 := pow_le_pow_right₀ hx' (by norm_num)
  constructor
  · intro i
    have hNear := near_ratio (D:=D) (J:=J) (nhood J) hbig (hz' i) hg (ha i).2
      (by positivity) hWD hn (Finset.erase_subset 0 _) (Finset.notMem_erase 0 _)
    rw [eJ,eR,show -((1/(8*X))*X^16)/2 = -(X^15/16) by field_simp; norm_num] at hNear
    have hcomp : 2*X^9+1 ≤ Real.exp (X^15/32) := by
      have hh : 64^2 ≤ X^6 := le_trans (pow_le_pow_left₀ (by positivity) hx 2) (pow_le_pow_right₀ hx' (by norm_num))
      have hm := mul_le_mul_of_nonneg_left hh (show 0≤X^9 by positivity)
      rw [← pow_add] at hm; norm_num1 at hm
      have hs : 2*X^9+1≤ X^15/32 + 1 := by linarith
      exact hs.trans (Real.add_one_le_exp _)
    apply hNear.trans
    apply (mul_le_mul_of_nonneg_right hcomp (Real.exp_pos _).le).trans
    rw [expo_merge, show X^15/32 + -(X^15/16) = -((d:ℝ)^15)/32 by change X^15/32+-(X^15/16) = -(X^15)/32; ring]
  constructor
  · intro i
    let G := nhood (2*D) \ nhood J
    let W := Real.exp (-(X^34)/4)
    have h (j : ℤ) (hj : j∈G) : ratio t D (delta s t i) j ≤ W := by
      obtain ⟨hk,hv⟩ := Finset.mem_sdiff.mp hj
      have hu := tail_ratio (hz' i) (show s≤t by exact_mod_cast he) (ha i).2
        (by positivity) hWD hn (show 1 ≤ J from Nat.one_le_pow _ _ (by omega))
        (fun hh => hv (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hk).1, hh⟩))
      convert hu using 2
      -- congr unfolded W already
      rw [eJ,eR]; ring
    have hh := Finset.sum_le_sum h
    rw [Finset.sum_const,nsmul_eq_mul] at hh
    refine hh.trans ?_
    have hm : G.card ≤ 4*D+1 := by
      have h := Finset.card_le_card (Finset.Subset.trans (Finset.sdiff_subset) (Finset.erase_subset _ (rad (2*D))) : G ⊆ rad (2*D))
      rw [rad_card] at h
      omega
    apply (mul_le_mul_of_nonneg_right (show (G.card:ℝ)≤Real.exp (3*P) from
      le_trans (by exact_mod_cast hm : (G.card:ℝ)≤4*D+1) hz.2) (Real.exp_pos _).le).trans
    unfold r
    rw [expo_merge]
    apply Real.exp_le_exp.mpr
    rw [show X^34=P*X*X by rw [eP]; ring]
    have hi : 4*(H+15) ≤ X*X := by nlinarith
    have h := mul_le_mul_of_nonneg_left hi (show 0≤P by positivity)
    linarith
  constructor
  · intro i
    exact center_ratio_bound (ha i).1 (ha i).2 (by positivity) hWD' hn
  have hq : q ≤ 1/2 := by
    have ep : q = (Real.exp (X^15/32))⁻¹ := by unfold q; rw [neg_div, Real.exp_neg]
    rw [ep, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    have e := Real.add_one_le_exp (X^15/32)
    norm_num
    linarith
  refine ⟨(Real.exp_pos _).le, hq, (Real.exp_pos _).le, ?_, ?_, ?_, ?_, he.trans hmax, hmax⟩
  · exact mul_nonneg (by positivity) (Real.exp_pos _).le
  · unfold q r
    rw [← Real.exp_nat_mul, eK, eP]
    apply Real.exp_le_exp.mpr
    have h : H+12 ≤ X/32 := by linarith
    change X^18 * (-(X^15)/32) ≤ -(H+12)*X^32
    calc
      _ = -(X/32)*X^32 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · unfold r
    apply Real.exp_le_exp.mpr
    rw [div_le_iff₀ (sq_pos_of_pos hspos)]
    have hr : (H+12)*P*(2*R) ≤ 4*(L:ℝ)^2 := by -- cast!
      have hz : H+12 ≤ X := by linarith
      rw [eP, eL]
      have h := mul_le_mul_of_nonneg_right hz (show 0≤ X^32*(2*(R:ℝ)) by positivity)
      rw [show (R:ℝ)=X^16 from eR] at *
      have hx2 : X^49 ≤ X^52 := pow_le_pow_right₀ hx' (by norm_num)
      calc
        _ ≤ X*(X^32*(2*X^16)) := by linarith
        _ = 2*X^49 := by ring
        _ ≤ 4*(X^26)^2 := by rw [← pow_mul]; change 2*X^49≤4*X^52; linarith only [hx2, show (0:ℝ)≤X^52 by positivity]
    have hh := mul_le_mul_of_nonneg_left hWD' (show 0≤(H+12)*P by dsimp [P]; positivity)
    have h := mul_le_mul_of_nonneg_right hr (show 0≤(D:ℝ) by positivity)
    linarith
  · have h : (R:ℝ)≤P := by rw [eP,eR]; exact pow_le_pow_right₀ hx' (by norm_num)
    unfold C
    rw [show 4*P=3*P+P by ring, Real.exp_add]
    gcongr
    exact hz.1

end Fourier

end IntegerMultiplication
end Computability
end OAI
