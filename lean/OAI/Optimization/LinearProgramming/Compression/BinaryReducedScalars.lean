import OAI.Optimization.LinearProgramming.Compression.BinaryGCD
import OAI.Optimization.LinearProgramming.Compression.BinaryGCDConcrete
import OAI.Optimization.LinearProgramming.Compression.ProjectionCramer
import OAI.Optimization.LinearProgramming.RAM.Array
import Mathlib.Tactic

/-! # Canonical rational numerator and denominator as RAM scalars

Save the original signed numerator and positive denominator, compute the gcd
of their magnitudes, and divide both saved integers exactly. Every quotient
appearing at the output is an integer in the canonical reduced representation. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM

/-- Dividing the two original integers by the positive gcd produces exactly
the two canonical integer scalars. -/
theorem gcd_divisions_eq_rat_fields (p : ℤ) {q : ℕ} (hq : 0 < q) :
    (p : ℚ) / (p.natAbs.gcd q : ℕ) = (((p : ℚ) / (q : ℚ)).num : ℚ) ∧
    (q : ℚ) / (p.natAbs.gcd q : ℕ) = (((p : ℚ) / (q : ℚ)).den : ℚ) := by
  have heq : (p : ℚ) / (q : ℚ) = mkRat p q := by
    rw [← Rat.divInt_ofNat, Rat.divInt_eq_div, Int.cast_natCast]
  rw [heq, Rat.num_mkRat, Rat.den_mkRat, Nat.gcd_comm q p.natAbs]
  simp only [hq.ne', ↓reduceIte]
  have hd : ((p.natAbs.gcd q : ℕ) : ℤ) ∣ p := by
    apply Int.natAbs_dvd_natAbs.mp
    simpa only [Int.natAbs_natCast] using Nat.gcd_dvd_left p.natAbs q
  constructor
  · have h := (Int.cast_div_charZero (k := ℚ) hd).symm
    simpa only [Int.cast_natCast] using h
  · exact (Nat.cast_div_charZero (K := ℚ) (Nat.gcd_dvd_right p.natAbs q)).symm

private def magnitudeGuard : Block :=
  .branch (.scalarLT 0 8) (.op (.sub 0 8 0)) .skip

private theorem magnitudeGuard_spec (m : Memory ℚ) (p : ℤ) {P : ℚ → Prop}
    (hm : m.AllData P) (hp : m.data 0 = (p : ℚ)) (hz : m.data 8 = 0)
    (hs : P (p.natAbs : ℚ)) :
    ∃ (n : ℕ) (s : Memory ℚ), Block.Eval (Memory.AllData P) magnitudeGuard m n s ∧ n ≤ 3 ∧
      s.data 0 = (p.natAbs : ℚ) ∧ (∀ i, i ≠ 0 → s.data i = m.data i) ∧ s.index = m.index := by
  by_cases h : p < 0
  · have hq : (p : ℚ) < 0 := by exact_mod_cast h
    have hcast : m.data 8 - m.data 0 = (p.natAbs : ℚ) := by
      rw [hz, hp, zero_sub]
      simpa only [Int.cast_neg, Int.cast_natCast] using congrArg (fun n : ℤ => (n : ℚ))
        ((Int.natCast_natAbs p).trans (abs_of_neg h)).symm
    have e := Block.Eval.op_sub m 0 8 0 hm (hm.putData 0 (hcast ▸ hs))
    exact ⟨3, _, .branchTrue (by simp [Cond.test, hp, hz, hq]) e, le_rfl,
      (Memory.putData_same ..).trans hcast, fun i hi => Memory.putData_ne _ hi _, rfl⟩
  · have hq : ¬ (p : ℚ) < 0 := by exact_mod_cast h
    have hcast : (p : ℚ) = (p.natAbs : ℚ) := by
      simpa only [Int.cast_natCast] using congrArg (fun n : ℤ => (n : ℚ))
        ((Int.natCast_natAbs p).trans (abs_of_nonneg (le_of_not_gt h))).symm
    exact ⟨1, m, .branchFalse (by simp [Cond.test, hp, hz, hq]) (.skip hm), by decide,
      hp.trans hcast, fun _ _ => rfl, rfl⟩

private def saveSignedPair : Block :=
  .seq (.op (.copy 6 0)) (.seq (.op (.copy 7 1)) (.op (.const 8 0)))

private theorem saveSignedPair_spec (m : Memory ℚ) {P : ℚ → Prop}
    (hm : m.AllData P) (hzero : P 0) :
    ∃ s, Block.Eval (Memory.AllData P) saveSignedPair m 3 s ∧
      s.data 0 = m.data 0 ∧ s.data 1 = m.data 1 ∧ s.data 6 = m.data 0 ∧
      s.data 7 = m.data 1 ∧ s.data 8 = 0 ∧ (∀ i, 9 ≤ i → s.data i = m.data i) ∧
      s.index = m.index := by
  let s := m.putData 6 (m.data 0)
  let t := s.putData 7 (s.data 1)
  let z := t.putData 8 0
  have e₁ := Block.Eval.op_copy m 6 0 hm (hm.putData 6 (hm 0))
  have hs : s.AllData P := e₁.safe_end
  have e₂ := Block.Eval.op_copy s 7 1 hs (hs.putData 7 (hs 1))
  have ht : t.AllData P := e₂.safe_end
  have e₃ := Block.Eval.op_const t 8 0 ht (ht.putData 8 hzero)
  refine ⟨z, e₁.seq (e₂.seq e₃), ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  all_goals try (solve | simp [z, t, s])
  intro i hi
  simp [z, t, s, show i ≠ 8 by omega, show i ≠ 7 by omega, show i ≠ 6 by omega]

private def divideSavedPair : Block :=
  .seq (.op (.copy 2 0)) (.seq (.op (.div 0 6 2)) (.op (.div 1 7 2)))

private theorem divideSavedPair_spec (m : Memory ℚ) (p : ℤ) {q : ℕ} (hq : 0 < q) {P : ℚ → Prop}
    (hm : m.AllData P) (h0 : m.data 0 = (p.natAbs.gcd q : ℕ))
    (h6 : m.data 6 = (p : ℚ)) (h7 : m.data 7 = (q : ℚ))
    (hn : P (((p : ℚ)/(q : ℚ)).num : ℚ)) (hd : P (((p : ℚ)/(q : ℚ)).den : ℚ)) :
    ∃ z, Block.Eval (Memory.AllData P) divideSavedPair m 3 z ∧
      z.data 0 = (((p : ℚ)/(q : ℚ)).num : ℚ) ∧ z.data 1 = (((p : ℚ)/(q : ℚ)).den : ℚ) ∧
      (∀ i, 3 ≤ i → z.data i = m.data i) ∧ z.index = m.index := by
  let s := m.putData 2 (m.data 0)
  let t := s.putData 0 (s.data 6 / s.data 2)
  let z := t.putData 1 (t.data 7 / t.data 2)
  have hpos : (0 : ℚ) < (p.natAbs.gcd q : ℕ) := by exact_mod_cast Nat.gcd_pos_of_pos_right p.natAbs hq
  have hs0 : s.data 2 ≠ 0 := by simpa only [s, Memory.putData_same, h0] using hpos.ne'
  obtain ⟨hcanonN, hcanonD⟩ := gcd_divisions_eq_rat_fields p hq
  have hsN : s.data 6 / s.data 2 = (((p : ℚ)/(q : ℚ)).num : ℚ) := by
    simpa [s, h0, h6] using hcanonN
  have htD : t.data 7 / t.data 2 = (((p : ℚ)/(q : ℚ)).den : ℚ) := by
    simpa [t, s, h0, h7] using hcanonD
  have e₁ := Block.Eval.op_copy m 2 0 hm (hm.putData 2 (hm 0))
  have hs : s.AllData P := e₁.safe_end
  have e₂ := Block.Eval.op_div s 0 6 2 hs0 hs (hs.putData 0 (hsN ▸ hn))
  have ht : t.AllData P := e₂.safe_end
  have e₃ := Block.Eval.op_div t 1 7 2 (by simpa [t] using hs0) ht (ht.putData 1 (htD ▸ hd))
  refine ⟨z, e₁.seq (e₂.seq e₃), ?_, ?_, ?_, rfl⟩
  · simpa [z, t] using hsN
  · exact (Memory.putData_same ..).trans htD
  · intro i hi
    simp [z, t, s, show i ≠ 0 by omega, show i ≠ 1 by omega, show i ≠ 2 by omega]


/-- Copy the signed input to permanent cells, reduce its magnitude pair by
Euclid's algorithm, and divide the signed inputs by their gcd. -/
def reducedScalarPairBlock : Block :=
  .seq saveSignedPair (.seq magnitudeGuard (.seq euclidGCDBlock divideSavedPair))

/-- From a signed integer in data 0 and a positive denominator in data 1,
return their canonical reduced integer representatives in those same two
cells, including all sign, branch, division and copying steps. -/
theorem reducedScalarPairBlock_spec (m : Memory ℚ) (p : ℤ) (q k : ℕ) {P : ℚ → Prop}
    (hm : m.AllData P) (hp : m.data 0 = (p : ℚ)) (hqv : m.data 1 = (q : ℚ))
    (hk : m.index 0 = k) (hq : 0 < q) (hpK : p.natAbs < 2^k) (hqK : q < 2^k)
    (hP : ∀ z : ℤ, z.natAbs ≤ 2^(2*k+2) → P (z : ℚ)) :
    ∃ (n : ℕ) (z : Memory ℚ), Block.Eval (Memory.AllData P) reducedScalarPairBlock m n z ∧
      n ≤ 2*k*(16*k+17)+10 ∧ z.data 0 = (((p : ℚ)/(q : ℚ)).num : ℚ) ∧
      z.data 1 = (((p : ℚ)/(q : ℚ)).den : ℚ) ∧ (∀ i, 9 ≤ i → z.data i = m.data i) ∧
      (∀ i, i ≠ 1 → z.index i = m.index i) := by
  have pNat (v : ℕ) (h : v ≤ 2^(2*k+2)) : P (v : ℚ) := by
    simpa only [Int.cast_natCast] using hP (v : ℤ) (by simpa only [Int.natAbs_natCast] using h)
  have hcap : 2^k ≤ 2^(2*k+2) := Nat.pow_le_pow_right (by decide) (by omega)
  have hz : P 0 := by simpa only [Nat.cast_zero] using pNat 0 (Nat.zero_le _)
  obtain ⟨s, es, hs0, hs1, hs6, hs7, hs8, fs, is'⟩ := saveSignedPair_spec m hm hz
  obtain ⟨n, t, et, hn, habs, ft, it⟩ :=
    magnitudeGuard_spec s p es.safe_end (hs0.trans hp) hs8 (pNat _ (hpK.le.trans hcap))
  obtain ⟨j, u, eu, hj, hg, _, fu, iu⟩ := euclidGCDBlock_spec t p.natAbs q k et.safe_end habs
    ((ft 1 (by decide)).trans (hs1.trans hqv)) ((congrFun it 0).trans ((congrFun is' 0).trans hk))
    ((ft 8 (by decide)).trans hs8) hpK hqK pNat
  have height : ((p : ℚ)/(q : ℚ)).num.natAbs ≤ p.natAbs ∧ ((p : ℚ)/(q : ℚ)).den ≤ q := by
    simpa only [Int.cast_natCast, Int.natAbs_natCast] using
      reduced_fraction_height p (q : ℤ) (by exact_mod_cast hq.ne')
  obtain ⟨z, ez, hN, hD, fz, iz⟩ := divideSavedPair_spec u p hq eu.safe_end hg
    ((fu 6 (by decide)).trans ((ft 6 (by decide)).trans (hs6.trans hp)))
    ((fu 7 (by decide)).trans ((ft 7 (by decide)).trans (hs7.trans hqv)))
    (hP _ (height.1.trans (hpK.le.trans hcap))) (pNat _ (height.2.trans (hqK.le.trans hcap)))
  refine ⟨3+(n+(j+3)), z, es.seq (et.seq (eu.seq ez)), by omega, hN, hD, ?_, ?_⟩
  · intro i hi
    exact (fz i (by omega)).trans ((fu i (by omega)).trans ((ft i (by omega)).trans (fs i hi)))
  · intro i hi
    exact (congrFun iz i).trans ((iu i hi).trans ((congrFun it i).trans (congrFun is' i)))

/-- Standalone normalization program with no quotient or gcd instruction. -/
def reducedScalarPairProgram : Program := reducedScalarPairBlock.compile 0 ++ [.halt 0]

/-- The returned scalars are the canonical integer numerator and denominator
and every register in the genuine run has bounded rational encoding length. -/
theorem reducedScalarPairProgram_trace (p : ℤ) (q k : ℕ) (hq : 0 < q)
    (hpK : p.natAbs < 2^k) (hqK : q < 2^k) :
    ∃ (steps : ℕ) (t : Fin (steps+1) → State ℚ), steps ≤ 2*k*(16*k+17)+11 ∧
      Trace reducedScalarPairProgram (start [k] [(p : ℚ), (q : ℚ)]) steps t ∧
      (t (Fin.last steps)).output = some 0 ∧
      (t (Fin.last steps)).data 0 = (((p : ℚ)/(q : ℚ)).num : ℚ) ∧
      (t (Fin.last steps)).data 1 = (((p : ℚ)/(q : ℚ)).den : ℚ) ∧
      ∀ i, scalarBound (2*k+5) (t i) := by
  let m := (start [k] [(p : ℚ), (q : ℚ)]).memory
  let P := fun z : ℚ => ratBits z ≤ 2*k+5
  have hP (v : ℤ) (hv : v.natAbs ≤ 2^(2*k+2)) : P (v : ℚ) := by
    have hmono : v.natAbs.log2 ≤ (2^(2*k+2)).log2 := by
      simpa only [Nat.log2_eq_log_two] using Nat.log_mono_right (b := 2) hv
    have hlog : v.natAbs.log2 ≤ 2*k+2 := hmono.trans_eq Nat.log2_two_pow
    simp only [P, ratBits, Rat.num_intCast, Rat.den_intCast, show Nat.log2 1 = 0 from rfl, Nat.add_zero]
    omega
  have hcap : 2^k ≤ 2^(2*k+2) := Nat.pow_le_pow_right (by decide) (by omega)
  have hm : m.AllData P := by
    intro i
    match i with
    | 0 => exact hP p (hpK.le.trans hcap)
    | 1 =>
      change P (q : ℚ)
      have h := hP (q : ℤ) (by simpa only [Int.natAbs_natCast] using hqK.le.trans hcap)
      simpa only [Int.cast_natCast] using h
    | _+2 =>
      change P 0
      have h := hP 0 (Nat.zero_le _)
      simpa only [Int.cast_zero] using h
  obtain ⟨steps, z, he, ht, hn, hd, _⟩ :=
    reducedScalarPairBlock_spec m p q k hm rfl rfl rfl hq hpK hqK hP
  obtain ⟨t, htrace, hout, hmem, hsafe⟩ := he.halted_trace (tag := 0)
  exact ⟨steps+1, t, by omega, htrace, hout,
    (congrArg (fun s : Memory ℚ => s.data 0) hmem).trans hn,
    (congrArg (fun s : Memory ℚ => s.data 1) hmem).trans hd, hsafe⟩

end Compression
end LinearProgramming
end Optimization
end OAI
