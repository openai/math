import OAI.Optimization.LinearProgramming.Geometry.PowerRangeRAM
import OAI.Optimization.LinearProgramming.Geometry.TaylorSetup

/-! Composition of the bounded range scan and the two actual Taylor kernels. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace PowerRAM

open RAM

private abbrev Within (W : ℕ) (m : Memory ℚ) := ∀ i, ratBits (m.data i) ≤ W

/-- A refinement of the memory predicate can be forgotten without changing the
program, time, output, or any state of the witnessed execution. -/
theorem weaken {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {P Q : Memory K → Prop} {b : Block} {s t k} (h : Block.Eval P b s k t)
    (hPQ : ∀ m, P m → Q m) : Block.Eval Q b s k t := by
  induction h with
  | skip a => exact .skip (hPQ _ a)
  | op a c e => exact .op (hPQ _ a) (hPQ _ c) e
  | seq _ _ a b => exact .seq a b
  | branchTrue h _ a => exact .branchTrue h a
  | branchFalse h _ a => exact .branchFalse h a
  | loopFalse h a => exact .loopFalse h (hPQ _ a)
  | loopTrue h _ _ a b => exact .loopTrue h a b

private theorem mono {b : Block} {s t k W W'} (h : Block.Eval (Within W) b s k t)
    (le : W ≤ W') : Block.Eval (Within W') b s k t := weaken h (fun _ hs i => (hs i).trans le)

private theorem write {W : ℕ} {m : Memory ℚ} (h : Within W m) (j : ℕ) {q : ℚ}
    (hq : ratBits q ≤ W) : Within W (m.putData j q) := by
  intro k
  by_cases e : k=j
  · simpa [e] using hq
  · simpa [e] using h k

/-- Compute the two loop counts B+1 and B+6 in the address bank. -/
def counts : Block := Block.straight
  [.incr 3 0, .incr 1 3, .incr 1 1, .incr 1 1, .incr 1 1, .incr 1 1]

private theorem run_counts (m : Memory ℚ) (B W : ℕ) (hb : m.index 0 = B) (hm : Within W m) :
    ∃ n, Block.Eval (Within W) counts m 6 n ∧ n.data = m.data ∧
      n.index 3 = B+1 ∧ n.index 1 = B+6 ∧
        ∀ j, j ≠ 1 → j ≠ 3 → n.index j = m.index j := by
  let m₁ := m.putIndex 3 (m.index 0+1)
  let m₂ := m₁.putIndex 1 (m₁.index 3+1)
  let m₃ := m₂.putIndex 1 (m₂.index 1+1)
  let m₄ := m₃.putIndex 1 (m₃.index 1+1)
  let m₅ := m₄.putIndex 1 (m₄.index 1+1)
  let m₆ := m₅.putIndex 1 (m₅.index 1+1)
  have e₁ : Block.Eval (Within W) (.op (.incr 3 0)) m 1 m₁ := .op hm hm (fun _ => rfl)
  have e₂ : Block.Eval (Within W) (.op (.incr 1 3)) m₁ 1 m₂ := .op hm hm (fun _ => rfl)
  have e₃ : Block.Eval (Within W) (.op (.incr 1 1)) m₂ 1 m₃ := .op hm hm (fun _ => rfl)
  have e₄ : Block.Eval (Within W) (.op (.incr 1 1)) m₃ 1 m₄ := .op hm hm (fun _ => rfl)
  have e₅ : Block.Eval (Within W) (.op (.incr 1 1)) m₄ 1 m₅ := .op hm hm (fun _ => rfl)
  have e₆ : Block.Eval (Within W) (.op (.incr 1 1)) m₅ 1 m₆ := .op hm hm (fun _ => rfl)
  refine ⟨m₆, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.skip hm)))))),
    rfl, ?_, ?_, ?_⟩
  · simp [m₆,m₅,m₄,m₃,m₂,m₁,hb]
  · simp [m₆,m₅,m₄,m₃,m₂,m₁,hb]
  · intro j h₁ h₃
    simp [m₆,m₅,m₄,m₃,m₂,m₁,h₁,h₃]

/-- Cell 14 receives the scaled rational Taylor estimate or zero when clipped.
Address 3 already contains the exponent of the output-grid denominator. -/
def rawBlock : Block := .seq PowerRangeRAM.block <| .seq counts <| .seq TaylorRAM.logBlock <|
  .seq (.op (.mul 2 12 0)) <| .seq TaylorRAM.expBlock (.op (.mul 14 9 0))

def logWidth (H B : ℕ) (θ : ℚ) : ℕ := PowerRangeRAM.width H B θ + 100*(B+6+10)^2

/-- Bit size of the reduced Taylor argument, independent of old scratch registers. -/
def argumentWidth (B : ℕ) (θ : ℚ) : ℕ :=
  let M := B+6
  3 + 2*(ratBits θ + 2*M*(2*M+2) + 2*M + 1)

def seriesWidth (H B : ℕ) (θ : ℚ) : ℕ :=
  logWidth H B θ + argumentWidth B θ + 100*(B+6+argumentWidth B θ+10)^2

def rawWidth (H B : ℕ) (θ : ℚ) : ℕ := seriesWidth H B θ + (3+4*B)

/-- Previous scratch contents enter the scalar-size bound additively, so the
bound can be iterated along an entire row without increasing the degree. -/
theorem rawWidth_additive (H B : ℕ) (θ : ℚ) : rawWidth H B θ = H + rawWidth 0 B θ := by
  simp [rawWidth,seriesWidth,logWidth,PowerRangeRAM.width,Nat.add_assoc]

private theorem log_two_truncation_unit (B : ℕ) :
    0 ≤ Compression.logTruncation (2 : ℚ) (B+6) ∧
    Compression.logTruncation (2 : ℚ) (B+6) ≤ 1 := by
  have h := Compression.abs_log_sub_logTruncation (z := 2) (by norm_num) le_rfl (B+6)
  have h₀ := Compression.two_thirds_le_logTruncation_two (M := B+6) (by omega)
  have h₁ := (abs_le.mp h).1
  rw [pow_add] at h₁
  norm_num only [one_div, inv_pow] at h₁
  have he : (1/2:ℝ)^(B+6) ≤ 1/64 := by
    rw [pow_add]
    norm_num
    linarith [pow_le_one₀ (by norm_num : 0 ≤ (1/2:ℝ)) (by norm_num : (1/2:ℝ) ≤ 1) (n := B)]
  have hnonneg : 0 ≤ Compression.logTruncation (2 : ℝ) (B+6) := by linarith
  have hle : Compression.logTruncation (2 : ℝ) (B+6) ≤ 1 := by
    have hp := (abs_le.mp h).1
    linarith [Real.log_two_lt_d9]
  have hc := Compression.cast_logTruncation (2 : ℚ) (B+6)
  norm_num only [Rat.cast_ofNat] at hc
  rw [← hc] at hnonneg hle
  exact ⟨by exact_mod_cast hnonneg, by exact_mod_cast hle⟩

/-- The input matrix, compressed minor table, and calling context can reside
above this routine's scalar and address scratch windows. -/
structure Frame (m n : Memory ℚ) : Prop where
  data : ∀ j, 20 < j → n.data j = m.data j
  index : ∀ j, 5 < j → n.index j = m.index j

theorem run_rawBlock (m : Memory ℚ) (H B : ℕ) (θ : ℚ) (hb : m.index 0 = B)
    (hi : m.data 0 = θ) (hθ : θ ≤ 0) (hm : ∀ j, ratBits (m.data j) ≤ H) :
    ∃ n k, k ≤ 25*B+143 ∧
      Block.Eval (fun v => ∀ j, ratBits (v.data j) ≤ rawWidth H B θ) rawBlock m k n ∧
      n.index 3 = B+1 ∧ (n.data 14 = if θ < -(B : ℚ) then 0 else reducedPowerApprox θ B) ∧
      Frame m n := by
  let M := B+6
  let L := logWidth H B θ
  let S := seriesWidth H B θ
  let W := rawWidth H B θ
  have hRL : PowerRangeRAM.width H B θ ≤ L := Nat.le_add_right _ _
  have hL₀ : 100*(M+10)^2 ≤ L := Nat.le_add_left _ _
  have hLS : L ≤ S := by dsimp only [S,seriesWidth,L]; omega
  have hAS : argumentWidth B θ ≤ S := by dsimp only [S,seriesWidth]; omega
  have hS₀ : 100*(M+argumentWidth B θ+10)^2 ≤ S := Nat.le_add_left _ _
  have hSW : S ≤ W := Nat.le_add_right _ _
  have hLW : L ≤ W := hLS.trans hSW
  obtain ⟨u,k,hk,er,hout⟩ := PowerRangeRAM.run_block m B H θ hi hb hθ hm
  have hu : Within L u := fun j => (er.safe_end.1 j).trans hRL
  have huB : u.index 0 = B := (er.safe_end.2.index 0 (by decide)).trans hb
  obtain ⟨v, ec, hdata, hkgrid, hM, fc⟩ := run_counts u B L huB hu
  obtain ⟨a, el, hlog, fl⟩ := TaylorRAM.run_logBlock v M L hM ec.safe_end hL₀
  have a12 : a.data 12 = u.data 12 := (fl.data 12 (by decide)).trans (congrFun hdata 12)
  have a9 : a.data 9 = u.data 9 := (fl.data 9 (by decide)).trans (congrFun hdata 9)
  have a3 : a.index 3 = B+1 := (fl.index 3 (by decide)).trans hkgrid
  have a1 : a.index 1 = M := (fl.index 1 (by decide)).trans hM
  have hfrac : 0 ≤ a.data 12 ∧ a.data 12 ≤ 1 := by
    rw [a12]
    by_cases h : θ < -(B : ℚ)
    · rw [(hout.saturated h).2.2]; norm_num
    · rw [(hout.reduced (le_of_not_gt h)).2.2]
      exact ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  let x := a.data 12 * a.data 0
  have hlogUnit := log_two_truncation_unit B
  have hxu : 0 ≤ x ∧ x ≤ 1 := by
    change 0 ≤ a.data 12 * a.data 0 ∧ a.data 12 * a.data 0 ≤ 1
    rw [hlog]
    exact ⟨mul_nonneg hfrac.1 hlogUnit.1,
      (mul_le_mul hfrac.2 hlogUnit.2 hlogUnit.1 zero_le_one).trans_eq (one_mul _)⟩
  have hx : ratBits x ≤ argumentWidth B θ := by
    by_cases h : θ < -(B : ℚ)
    · have hz : x = 0 := by dsimp only [x]; rw [a12, (hout.saturated h).2.2, zero_mul]
      rw [hz]
      change 3 ≤ 3+_
      omega
    · have heq : x = Int.fract θ * Compression.logTruncation 2 M := by
        dsimp only [x]; rw [a12, (hout.reduced (le_of_not_gt h)).2.2, hlog]
      have hd := reducedTaylorArgument_den_size θ M
      rw [← heq] at hd
      have hθd := TaylorRAM.size_le_bits θ
      have hd' : x.den.size ≤ ratBits θ + 2*M*(2*M+2)+2*M+1 := by omega
      have hnum := Compression.numerator_le_mul_den (n := 1) hxu.1 (by simpa using hxu.2)
      rw [one_mul] at hnum
      exact TaylorRAM.bits_of_size hd' ((Nat.size_le_size hnum).trans hd')
  let a' := a.putData 2 x
  have haS : Within S a := fun j => (el.safe_end j).trans hLS
  have ex : Block.Eval (Within S) (.op (.mul 2 12 0)) a 1 a' :=
    .op haS (write haS 2 (hx.trans hAS)) (fun _ => rfl)
  have hXS : 100*(M+ratBits x+10)^2 ≤ S := by
    apply le_trans _ hS₀
    gcongr
  obtain ⟨b, ee, hsum, fe⟩ := TaylorRAM.run_expBlock a' M S x a1
    (by simp [a']) hxu.1 hxu.2 ex.safe_end hXS
  have b9 : b.data 9 = u.data 9 := (fe.data 9 (by decide)).trans
    (by simpa [a'] using a9)
  have b3 : b.index 3 = B+1 := (fe.index 3 (by decide)).trans a3
  let n := b.putData 14 (b.data 9 * b.data 0)
  have hscalebits : ratBits (b.data 9) ≤ 3+4*B := by
    rw [b9]
    by_cases h : θ < -(B : ℚ)
    · rw [(hout.saturated h).2.1]
      change 3 ≤ 3+4*B
      omega
    · rw [(hout.reduced (le_of_not_gt h)).2.1]
      obtain ⟨hlo,hhi⟩ := reducedPowerApprox_exponent_bound (le_of_not_gt h) hθ
      have hbAbs : ⌊θ⌋.natAbs ≤ B := by
        have hn := Int.ofNat_natAbs_of_nonpos hhi
        omega
      have hbits := Compression.ratBits_intPow_le (2 : ℚ) ⌊θ⌋
      rw [show ratBits 2 = 4 by rfl] at hbits
      omega
  have hprod : ratBits (b.data 9*b.data 0) ≤ W :=
    (Compression.ratBits_mul_le_add _ _).trans (by
      change _ ≤ S+(3+4*B)
      linarith only [hscalebits, ee.safe_end 0])
  have hbW : Within W b := fun j => (ee.safe_end j).trans hSW
  have ef : Block.Eval (Within W) (.op (.mul 14 9 0)) b 1 n :=
    .op hbW (write hbW 14 hprod) (fun _ => rfl)
  have erw : Block.Eval (Within W) PowerRangeRAM.block m k u :=
    weaken er (fun _ hh j => (hh.1 j).trans (hRL.trans hLW))
  refine ⟨n, _, ?_, .seq erw (.seq (mono ec hLW) (.seq (mono el hLW)
    (.seq (mono ex hSW) (.seq (mono ee hSW) ef)))), b3, ?_, ?_⟩
  · dsimp only [M]; omega
  · change (b.putData 14 (b.data 9*b.data 0)).data 14 = _
    rw [Memory.putData_same, b9, hsum]
    dsimp only [x]
    rw [a12, hlog]
    by_cases h : θ < -(B : ℚ)
    · simp [(hout.saturated h).2.1, h]
    · simp only [ite_eq_right h, (hout.reduced (le_of_not_gt h)).2.1,
        (hout.reduced (le_of_not_gt h)).2.2]
      rfl
  · constructor
    · intro j hj
      have hj₇ : 7 ≤ j := by omega
      calc
        n.data j = b.data j := by simp [n, show j ≠ 14 by omega]
        _ = a'.data j := fe.data _ hj₇
        _ = a.data j := by simp [a', show j ≠ 2 by omega]
        _ = v.data j := fl.data _ hj₇
        _ = u.data j := congrFun hdata _
        _ = m.data j := er.safe_end.2.data _ (by omega)
    · intro j hj
      have hj₀ : j ≠ 0 := by omega
      calc
        n.index j = b.index j := rfl
        _ = a'.index j := fe.index _ hj₀
        _ = a.index j := rfl
        _ = v.index j := fl.index _ hj₀
        _ = u.index j := fc _ (by omega) (by omega)
        _ = m.index j := er.safe_end.2.index _ (by omega)

/-- The composed scalar bound is a fixed polynomial in the numerical loop
parameter and the binary input lengths. -/
theorem rawWidth_polynomial (H B : ℕ) (θ : ℚ) :
    rawWidth H B θ ≤ 10000000 * (H + B + ratBits θ + 20)^4 := by
  let s := H+B+ratBits θ+20
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hs₂ : s ≤ s^2 := by simpa using Nat.pow_le_pow_right hs (show 1 ≤ 2 by decide)
  have hs₄ : s^2 ≤ s^4 := Nat.pow_le_pow_right hs (by decide)
  have hB : B+6+10 ≤ s := by dsimp [s]; omega
  have hR : PowerRangeRAM.width H B θ ≤ 8*s := by
    dsimp only [PowerRangeRAM.width,s]
    omega
  have hL : logWidth H B θ ≤ 108*s^2 := by
    have hb := Nat.pow_le_pow_left hB 2
    dsimp only [logWidth]
    omega
  have hθ : ratBits θ ≤ s := by dsimp [s]; omega
  have hM : B+6 ≤ s := by omega
  have hA : argumentWidth B θ ≤ 30*s^2 := by
    have hmul := Nat.mul_le_mul hM hM
    dsimp [argumentWidth]
    nlinarith only [hmul, hM, hθ, hs₂, hs]
  have hsum : B+6+argumentWidth B θ+10 ≤ 31*s^2 := by omega
  calc
    rawWidth H B θ ≤ 108*s^2+30*s^2+100*(31*s^2)^2+(3+4*B) := by
      unfold rawWidth seriesWidth
      gcongr
    _ ≤ 10000000*s^4 := by nlinarith only [hs₄,hs₂,hs,hB, Nat.zero_le (s^4)]

private theorem fractionalPower_zero (B : ℕ) : fractionalPowerApprox 0 B = 1 := by
  unfold fractionalPowerApprox expTruncation
  simp only [zero_mul]
  rw [Finset.sum_eq_single 0]
  · norm_num
  · intro i _ hi
    simp [zero_pow hi]
  · simp

/-- The following dyadic quantizer can consume cell 14 uniformly, including
both saturation and an exact pivot. -/
theorem roundedPower_eq_quantized_raw (θ : ℚ) (B : ℕ) :
    let raw := if θ < -(B : ℚ) then 0 else reducedPowerApprox θ B
    roundedPower θ B = (⌊(2 : ℚ)^(B+1) * max 0 (min raw 1)⌋₊ : ℚ) / (2 : ℚ)^(B+1) := by
  dsimp only
  by_cases hz : θ = 0
  · subst θ
    have hfalse : ¬(0 : ℚ) < -(B : ℚ) := by exact not_lt.mpr (neg_nonpos.mpr (by positivity))
    have hgrid : ⌊(2 : ℚ)^(B+1)⌋₊ = 2^(B+1) := by
      exact_mod_cast Nat.floor_natCast (R := ℚ) (2^(B+1))
    simp [hfalse, reducedPowerApprox, fractionalPower_zero, hgrid]
  · by_cases h : θ < -(B : ℚ)
    · simp [roundedPower, roundedPowerNumerator, hz, h]
    · simp only [roundedPower, roundedPowerNumerator, ite_eq_right hz, ite_eq_right h]
      rfl

end PowerRAM
end Geometry
end LinearProgramming
end Optimization
end OAI
