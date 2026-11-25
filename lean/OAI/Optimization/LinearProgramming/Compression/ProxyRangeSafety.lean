import OAI.Optimization.LinearProgramming.Compression.ProxyRangeSafetySteps

/-! All-register correctness of the capped upward/downward binary logarithm
range computation. The first power above the input may be squared once; its
exponent is charged to the input encoding, not the cutoff value. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.RAM OAI.Optimization.LinearProgramming.FieldTransfer RangeKernel

private theorem range_power_fits {a B fuel : ℕ} (ha : a ≤ 2*B) :
    ratBits ((2 : ℚ)^a) ≤ rangeHeadBits B fuel := by
  have hb : ratBits ((2 : ℚ)^a) ≤ a+3 := by exact_mod_cast natCast_ratBits_le (n := 2^a) le_rfl
  exact hb.trans (by dsimp [rangeHeadBits]; omega)

private theorem range_digit_fits {j B fuel : ℕ} (hj : j ≤ 2^fuel) :
    ratBits (j : ℚ) ≤ rangeHeadBits B fuel :=
  (natCast_ratBits_le hj).trans (by dsimp [rangeHeadBits]; omega)

private theorem safe_scan (n fuel B : ℕ) {mag : ℚ} (hm : 0 < mag) (hmag : ratBits mag ≤ B)
    (hn : n ≤ fuel) {s : State ℚ} {ptr a : ℕ} (hptr : 8 ≤ ptr)
    (ha : 0 < a) (hs : Scan s (normalizedMagnitude mag) ((2:ℚ)^a) n ptr)
    (hB : scalarBound (rangeHeadBits B fuel) s) :
    ∃ len ≤ 16*n+3, ∃ t,
      RegisterBoundedRun logRangeProgram s len t (rangeRegisterBound B fuel) ∧
      scalarBound (rangeHeadBits B fuel) t ∧
      (match rangeAnswer n (normalizedMagnitude mag) ((2:ℚ)^a) with
        | none => t.output = some 1
        | some (e,q) => Unwind t (normalizedMagnitude mag) ptr e q ∧ StackPrefix s t ptr) := by
  let z := normalizedMagnitude mag
  change Scan s z ((2:ℚ)^a) n ptr at hs
  change ∃ len ≤ 16*n+3, ∃ t,
    RegisterBoundedRun logRangeProgram s len t (rangeRegisterBound B fuel) ∧
      scalarBound (rangeHeadBits B fuel) t ∧
      (match rangeAnswer n z ((2:ℚ)^a) with
        | none => t.output = some 1
        | some (e,q) => Unwind t z ptr e q ∧ StackPrefix s t ptr)
  induction n generalizing s ptr a with
  | zero =>
    by_cases hz : z < (2:ℚ)^a
    · obtain ⟨t, ht, hu, hf⟩ := scan_base hs hz
      exact ⟨1, by omega, t, range_short_bound (by decide) hB ht, range_base_bound hs hz hB ht,
        by simpa only [rangeAnswer, ite_eq_left hz] using And.intro hu hf⟩
    · obtain ⟨t, ht, ho⟩ := scan_saturate hs (le_of_not_gt hz)
      exact ⟨3, by omega, t, range_short_bound (by decide) hB ht,
        range_saturate_bound hs (le_of_not_gt hz) hB ht, by simpa only [rangeAnswer, ite_eq_right hz] using ho⟩
  | succ n ih =>
    let p := (2 : ℚ)^a
    change Scan s z p (n+1) ptr at hs
    change ∃ len ≤ 16*(n+1)+3, ∃ t,
      RegisterBoundedRun logRangeProgram s len t (rangeRegisterBound B fuel) ∧
        scalarBound (rangeHeadBits B fuel) t ∧
        (match rangeAnswer (n+1) z p with
          | none => t.output = some 1
          | some (e,q) => Unwind t z ptr e q ∧ StackPrefix s t ptr)
    by_cases hz : z < p
    · obtain ⟨t, ht, hu, hf⟩ := scan_base hs hz
      exact ⟨1, by omega, t, range_short_bound (by decide) hB ht, range_base_bound hs hz hB ht,
        by simpa only [rangeAnswer, ite_eq_left hz] using And.intro hu hf⟩
    · have hle : p ≤ z := le_of_not_gt hz
      have hao : a ≤ B := (exponent_le_ratBits hm hle).trans hmag
      have hp : 1 < p := one_lt_pow₀ (by norm_num) ha.ne'
      have hpp : p*p = (2:ℚ)^(2*a) := by dsimp [p]; rw [two_mul, pow_add]
      have hppbits : ratBits (p*p) ≤ rangeHeadBits B fuel := by
        rw [hpp]; exact range_power_fits (by omega)
      obtain ⟨u,hsu,huh,hval,hmem⟩ := scan_push hptr hs hle
      have Ru := range_short_bound (by decide) hB hsu
      have Bu := range_push_bound hptr hs hle hB hppbits hsu
      have huh' : Scan u z ((2:ℚ)^(2*a)) n (ptr+1) := by simpa only [hpp] using huh
      have recur : ∃ len ≤ 16*n+3, ∃ t,
          RegisterBoundedRun logRangeProgram u len t (rangeRegisterBound B fuel) ∧
          scalarBound (rangeHeadBits B fuel) t ∧
          (match rangeAnswer n z ((2:ℚ)^(2*a)) with
           | none => t.output = some 1
           | some (e,q) => Unwind t z (ptr+1) e q ∧ StackPrefix u t (ptr+1)) := by
        apply ih (s := u) (ptr := ptr+1) (a := 2*a)
        all_goals first | exact huh' | exact Bu | omega
      obtain ⟨len,hlen,v,Rv,Bv,ret⟩ := recur
      rw [← hpp] at ret
      cases hres : rangeAnswer n z (p*p) with
      | none =>
        rw [hres] at ret
        exact ⟨7+len, by omega, v, Ru.appendSame Rv, Bv,
          by simpa only [rangeAnswer, ite_eq_right hz, hres] using ret⟩
      | some pair =>
        rcases pair with ⟨e,q⟩
        rw [hres] at ret
        obtain ⟨hvhead,hvstack⟩ := ret
        have hstack : v.data ptr = p := (hvstack ptr hptr (by omega)).trans hval
        have hspec := (powerSearch_spec n z (p*p) (one_le_normalizedMagnitude hm)
          (by nlinarith [sq_nonneg (p-1)])).2
        rw [← rangeAnswer_rat_eq, hres] at hspec
        obtain ⟨hq,hqz,_,he⟩ := hspec
        have hpow : q = (2:ℚ)^((2*a)*e) := by rw [hq, hpp, ← pow_mul]
        have he' : (2*a)*e ≤ B := (exponent_le_ratBits hm (hpow ▸ hqz)).trans hmag
        have hbits : ratBits (q*p) ≤ rangeHeadBits B fuel := by
          rw [hpow, show p = (2:ℚ)^a by rfl, ← pow_add]
          exact range_power_fits (by omega)
        have hrange : 2*e+1 ≤ 2^fuel := by
          have ht : 2*e+1 ≤ 2^(n+1) := by rw [pow_succ]; omega
          exact ht.trans (Nat.pow_le_pow_right (by decide) hn)
        have heven : ratBits (2*(e:ℚ)) ≤ rangeHeadBits B fuel := by
          exact_mod_cast range_digit_fits (B := B) (fuel := fuel) (j := 2*e) (by omega)
        have hodd : ratBits (2*(e:ℚ)+1) ≤ rangeHeadBits B fuel := by exact_mod_cast range_digit_fits (B := B) hrange
        obtain ⟨t,ht,hout,htmem⟩ := unwind_bit_exact hptr hvhead hstack
        let j : ℕ := if z < q*p then 6 else 9
        have hj : j ≤ 9 := by dsimp only [j]; split <;> decide
        have Rt := range_short_bound hj Bv ht
        have Bt := range_unwind_bound hptr hvhead hstack Bv hbits heven hodd ht
        have hf : StackPrefix s t ptr := fun i hi hic =>
          (htmem i hi hic).trans ((hvstack i hi (by omega)).trans (hmem i hi hic))
        refine ⟨(7+len)+j, by omega, t, (Ru.appendSame Rv).appendSame Rt, Bt, ?_⟩
        by_cases hc : z < q*p
        · rw [ite_eq_left hc] at hout
          simpa only [rangeAnswer, ite_eq_right hz, hres, ite_eq_left hc] using And.intro hout hf
        · rw [ite_eq_right hc] at hout
          simpa only [rangeAnswer, ite_eq_right hz, hres, ite_eq_right hc] using And.intro hout hf

/-- The range search has a terminating run with the input-sensitive scalar
bound at every prefix. -/
theorem logRangeProgram_boundedRun {mag : ℚ} (hm : 0 < mag) (fuel B : ℕ) (s : State ℚ)
    (hp : s.pc = 0) (ho : s.output = none) (hd : s.data 0 = mag) (hf : s.index 0 = fuel)
    (hb : scalarBound B s) :
    ∃ len ≤ 16*fuel+14, ∃ t tag,
      RegisterBoundedRun logRangeProgram s len t (rangeRegisterBound B fuel) ∧ t.output = some tag := by
  have hmag : ratBits mag ≤ B := hd ▸ hb 0
  obtain ⟨i,hi,u,hu,hscan⟩ := scan_init mag hm fuel s hp ho hd hf
  obtain ⟨R₀,B₀⟩ := range_init_bound (fuel := fuel) hi hb hu
  have hn : normalizedRangeInput mag = normalizedMagnitude mag := by
    by_cases h : mag < 1 <;> simp [normalizedRangeInput, normalizedMagnitude, h]
  rw [hn] at hscan
  obtain ⟨j,hj,v,R₁,B₁,hret⟩ := safe_scan fuel fuel B hm hmag le_rfl (s := u) (ptr := 8) (a := 1)
    (by decide) (by decide) (by simpa using hscan) B₀
  rw [pow_one] at hret
  cases hres : rangeAnswer fuel (normalizedMagnitude mag) 2 with
  | none =>
    rw [hres] at hret
    exact ⟨i+j, by omega, v, 1, R₀.appendSame R₁, hret⟩
  | some pair =>
    rcases pair with ⟨e,q⟩
    rw [hres] at hret
    obtain ⟨t, ht, hout, _, _, _⟩ := unwind_halt hret.1
    exact ⟨i+j+2, by omega, t, 0, (R₀.appendSame R₁).appendSame (range_short_bound (by decide) B₁ ht), hout⟩

/-- A fixed affine bound controls all scalar registers at every actually
reachable state, including live returns and both halted branches. -/
theorem logRangeProgram_scalarBound {mag : ℚ} (hm : 0 < mag) (fuel B : ℕ) (s : State ℚ)
    (hp : s.pc = 0) (ho : s.output = none) (hd : s.data 0 = mag) (hf : s.index 0 = fuel)
    (hb : scalarBound B s) {j : ℕ} {u : State ℚ} (hu : runExactly logRangeProgram s j = some u) :
    scalarBound (rangeRegisterBound B fuel) u := by
  obtain ⟨len, _, t, tag, hrun, hhalt⟩ := logRangeProgram_boundedRun hm fuel B s hp ho hd hf hb
  apply hrun.bound j _ u hu
  by_contra! hj
  have hj' : 0 < j - len := by omega
  rw [show j = len+(j-len) by omega, runExactly_add_series, hrun.execution, Option.bind_some] at hu
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hj'.ne'
  rw [hk, runExactly_succ_first] at hu
  simp [step, hhalt] at hu

/-- The explicit rational bound is affine in the precision fuel and the input
register encoding. -/
theorem rangeRegisterBound_le_polyBound (B fuel : ℕ) :
    rangeRegisterBound B fuel ≤ RAM.polyBound (rangeRegisterBound 1 1) 1 (B+fuel) := by
  unfold rangeRegisterBound rangeHeadBits RAM.polyBound
  ring_nf
  omega

/-- Correct range answer, actual work, and a linear rational register bound for
one trace starting with the canonical input. -/
theorem logRangeProgram_spec (fuel : ℕ) {mag : ℚ} (hm : 0 < mag) :
    ∃ len ≤ 16*fuel+14, ∃ t : Fin (len+1) → State ℚ,
      Trace logRangeProgram (start [fuel] [mag]) len t ∧
      (match (powerSearch fuel (normalizedMagnitude mag) 2).answer with
       | none => (t (Fin.last _)).output = some 1
       | some (e,q) => (t (Fin.last _)).output = some 0 ∧
          (t (Fin.last _)).data 0 = normalizedMagnitude mag ∧
          (t (Fin.last _)).data 3 = q ∧ (t (Fin.last _)).data 4 = (e : ℚ)) ∧
      ∀ i, scalarBound (RAM.polyBound (rangeRegisterBound 1 1) 1 (ratBits mag+fuel)) (t i) := by
  obtain ⟨len, hlen, t, ht, hout⟩ := logRangeProgram_exec fuel hm
  refine ⟨len, hlen, t, ht, hout, ?_⟩
  have hinit : scalarBound (ratBits mag) (start [fuel] [mag]) := by
    intro j; cases j with
    | zero => exact le_rfl
    | succ j =>
      change ratBits 0 ≤ ratBits mag
      rw [show ratBits 0 = 3 by decide]
      unfold ratBits; omega
  intro i a
  have hh := logRangeProgram_scalarBound hm fuel (ratBits mag) (start [fuel] [mag]) rfl rfl rfl rfl
    hinit (runExactly_of_trace ht i)
  exact (hh a).trans (rangeRegisterBound_le_polyBound _ _)

end Compression
end LinearProgramming
end Optimization
end OAI
