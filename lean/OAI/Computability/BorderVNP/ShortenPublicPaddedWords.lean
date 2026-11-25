import OAI.Computability.BorderVNP.ShortenPublicPaddedCapacity
import OAI.Computability.BorderVNP.ShortenEpochLocalRecords
import OAI.Computability.BorderVNP.PackedResources
import OAI.Computability.BorderVNP.ShortenPublicSegmentBudget

/-!
# Public identifier and count widths for stable shortening rectangles

Expanded local records bound the total cable-bit population, including inactive
cables. A single binary word can hold every stable row identifier and every
possible multiplied seed count. The bit length is logarithmic in the processor
parameters throughout the complete public history.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicCapacity

open Cover Epoch Crossing TeamScales Filter Finset
open scoped Classical

/-- Summed expanded records pay for every bit of every old cable, including
cables which are presently uncharged. -/
theorem totalWidth_le_records {D : ℕ} {P T : Type*} [Fintype P] [Fintype T]
    {bits : P → ℕ} (N : Network D P bits) (tile : N.Site → T) (prior payload : N.Site → ℕ)
    (cap : ℕ) (hc : ∀ t, localRecords N true prior payload (fun v => tile v=t) ≤ cap) :
    (∑ e, N.width e) ≤ Fintype.card T * cap := by
  have all := localRecords_near N true prior payload tile Finset.univ
  simp only [Finset.mem_univ] at all
  have widths : (∑ e, N.width e) ≤ localRecords N true prior payload (fun _ => True) := by
    simp only [localRecords,testedWidth,recordCost,↓reduceIte]
    have here := Finset.sum_le_sum (s := Finset.univ) fun e _ => Nat.le_add_left (N.width e) 1
    omega
  exact widths.trans (all.le.trans (by simpa using Finset.sum_le_sum (s := Finset.univ) fun t _ => hc t))

/-- Word width sufficient for both stable endpoint/edge pointers and the
entire multiplied seed pool. -/
def wordSize (sites edges multiplier tiles expanded : ℕ) :=
  Nat.clog 2 (1+sites+edges+multiplier*(tiles*expanded))

theorem wordSize_fits (sites edges multiplier tiles expanded : ℕ) :
    sites ≤ 2^wordSize sites edges multiplier tiles expanded ∧
      edges ≤ 2^wordSize sites edges multiplier tiles expanded ∧
      multiplier*(tiles*expanded) < 2^wordSize sites edges multiplier tiles expanded := by
  have h := Nat.le_pow_clog (by decide : 1<2) (1+sites+edges+multiplier*(tiles*expanded))
  unfold wordSize
  omega

/-- The ordinary address logarithm of §7 equals the binary ceiling logarithm. -/
theorem public_logWidth (n r : ℕ) : logWidth r n = Nat.clog 2 (2*n*r) := by
  unfold logWidth
  rw [← Real.natCeil_logb_natCast]
  norm_cast

/-- With at most a fixed polynomial in the physical length and team size
worth of bits and names, the chosen word width is an explicit constant
multiple of the paper's ordinary address logarithm. -/
theorem wordSize_le_logWidth {n r sites edges multiplier tiles expanded : ℕ}
    (hn : 1 ≤ n) (hr : 1 ≤ r) (hptr : sites+edges+1 ≤ 2*n*r)
    (htiles : tiles ≤ n*r) (hbits : expanded ≤ n) (hm : multiplier ≤ n) :
    wordSize sites edges multiplier tiles expanded ≤ 3*logWidth r n := by
  let U := 2*n*r
  have tilesU : tiles ≤ U := htiles.trans (by dsimp [U]; nlinarith)
  have hb : multiplier*(tiles*expanded) ≤ n*(U*n) := Nat.mul_le_mul hm (Nat.mul_le_mul tilesU hbits)
  have sup : 1+sites+edges+multiplier*(tiles*expanded) ≤ U^3 := by
    have un : 2*n ≤ U := by dsimp [U]; exact Nat.le_mul_of_pos_right _ hr
    have square : n*n + 1 ≤ U*U := by nlinarith [Nat.mul_le_mul un un]
    have use := Nat.mul_le_mul_left U square
    change sites+edges+1 ≤ U at hptr
    nlinarith only [hptr,hb,use]
  rw [public_logWidth]
  apply Nat.clog_le_of_le_pow
  change _ ≤ 2^(3*Nat.clog 2 U)
  rw [mul_comm 3 _,pow_mul]
  exact sup.trans (Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) U) 3)

variable {D m : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m)

/-- The exact static rectangle cap throughout the history, in the form used
by the sparse compiler. Its multiplier includes the K children of every node. -/
theorem joinedRows_real_bound {fan : ℕ} (hf : 1 ≤ fan) (rounds extra V bins : ℕ)
    (seeds : ℕ → ℕ → ℕ) (hs : ∀ t j, seeds t j ≤ V*bins) (initial : Shape) {t T j : ℕ}
    (ht : t<T) (hj : j<rounds) (A : ℝ) (ha : 0 ≤ A) {n r : ℕ}
    (hinit : (initial.volume V : ℝ) ≤ A*(r*(n : ℝ)^(9/10 : ℝ))) {α : ℝ} (hw : 1 ≤ width n α) :
    let old := epochRows e fan rounds extra seeds initial t
    let rows := (combineRows e fan (seeds t) (old.subdivide extra) j).parallel fan
    (rows.volume V : ℝ) ≤ A*(r*(n : ℝ)^(9/10 : ℝ))*
      ((epochFactor e fan rounds extra bins : ℝ)^T * width n α) := by
  intro old rows
  have h : (rows.volume V : ℝ) ≤ (epochFactor e fan rounds extra bins : ℝ)^T * initial.volume V := by
    exact_mod_cast joinedRows_le e hf rounds extra V bins seeds hs initial ht hj
  apply h.trans
  have hW : 1 ≤ (width n α : ℝ) := by exact_mod_cast hw
  calc
    _ ≤ (epochFactor e fan rounds extra bins : ℝ)^T * (A*(r*(n : ℝ)^(9/10 : ℝ))) := by gcongr
    _ ≤ _ := by
      let vol := A*(r*(n : ℝ)^(9/10 : ℝ))
      let G := (epochFactor e fan rounds extra bins : ℝ)^T
      change G*vol ≤ vol*(G*(width n α : ℝ))
      calc
        G*vol ≤ (G*vol)*(width n α : ℝ) := le_mul_of_one_le_right (by dsimp [G,vol]; positivity) hW
        _ = _ := by ring

/-- For all large lengths and all team sizes, the true static row-name range
is at most the ordinary processor address range. The fixed extra constant
for the initial grid is absorbed before any team size is selected. -/
theorem eventually_row_names {fan : ℕ} (hf : 1 ≤ fan) (rounds extra bins : ℕ)
    {α τ : ℝ} (hα : α < 1/1000) (hτ : 0 ≤ τ)
    (hg : τ * Real.logb 2 (epochFactor e fan rounds extra bins) ≤ α/10) (A : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, ∀ (V : ℕ) (seeds : ℕ → ℕ → ℕ) (initial : Shape),
      (∀ t j, seeds t j ≤ V*bins) →
      (initial.volume V : ℝ) ≤ A*(r*(n : ℝ)^(9/10 : ℝ)) →
      ∀ t < epochs τ n, ∀ j < rounds,
        let old := epochRows e fan rounds extra seeds initial t
        let rows := (combineRows e fan (seeds t) (old.subdivide extra) j).parallel fan
        rows.volume V ≤ r*n := by
  let G := epochFactor e fan rounds extra bins
  have tend := (tendsto_rpow_atTop (show 0 < (1/20:ℝ) by norm_num)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_ge_atTop 1,tend.eventually_ge_atTop A] with n hn hA
  intro r V seeds initial hs hi t ht j hj old rows
  have cap : (rows.volume V : ℝ) ≤ (G : ℝ)^epochs τ n * initial.volume V := by
    exact_mod_cast joinedRows_le e hf rounds extra V bins seeds hs initial ht hj
  have hG := epoch_growth_le (by exact_mod_cast epochFactor_pos e hf rounds extra bins : 1 ≤ (G : ℝ)) hn hτ hg
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 := zero_lt_one.trans_le hn'
  have he : (n : ℝ)^(α/10) ≤ (n : ℝ)^(1/20 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn' (by linarith)
  change A ≤ (n : ℝ)^(1/20 : ℝ) at hA
  have hcap := cap.trans (mul_le_mul (hG.trans he) hi (by positivity) (by positivity))
  have final : (rows.volume V : ℝ) ≤ (r : ℝ)*n := by
    apply hcap.trans
    calc
      _ ≤ (n : ℝ)^(1/20 : ℝ)*((n : ℝ)^(1/20 : ℝ)*(r*(n : ℝ)^(9/10 : ℝ))) := by gcongr
      _ = _ := by
        rw [show (n : ℝ)^(1/20 : ℝ)*((n : ℝ)^(1/20 : ℝ)*(r*(n : ℝ)^(9/10 : ℝ))) =
          r*((n : ℝ)^(1/20 : ℝ)*(n : ℝ)^(1/20 : ℝ)*(n : ℝ)^(9/10 : ℝ)) by ring,
          ←Real.rpow_add hn0,←Real.rpow_add hn0]
        norm_num
  exact_mod_cast final

end Shortening.PublicCapacity

end BorderVNP
end Computability
end OAI
