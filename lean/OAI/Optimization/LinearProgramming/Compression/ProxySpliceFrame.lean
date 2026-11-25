import OAI.Optimization.LinearProgramming.Compression.ProxyProgram
import OAI.Optimization.LinearProgramming.Compression.ProxyRangeFootprint

/-! Caller frames for the raw logarithm proxy and its three linking splices. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.RAM OAI.Optimization.LinearProgramming.FieldTransfer

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

namespace ProxyKernel

attribute [local simp]
  fetch0 fetch1 fetch2 fetch3 fetch4 fetch5 fetch33 fetch34
  fetch35 fetch36 fetch37 fetch38 fetch39 fetch40 fetch41 fetch42
  fetch43 fetch44 fetch45 fetch46 fetch47 fetch48 fetch49 fetch50
  fetch51 fetch52 fetch53 fetch54 fetch55 fetch116 fetch117 fetch118
  fetch119 fetch120
  fetch_small_jump fetch_restore_jump

/-- The prologue only writes the flag and precision below address slot six and
the scalar comparison constant in slot seven. -/
theorem proxy_prefix_frame {mag : K} {s t : State K} (hp : s.pc = 0) (ho : s.output = none)
    (hd : s.data 0 = mag)
    (hr : runExactly logProxyProgram s (if mag < 1 then 5 else 4) = some t) :
    PreservesRegisters 8 6 s t := by
  by_cases h : mag < 1 <;>
    simp [runExactly, step, execInstr, hp, ho, hd, h, State.putData, State.putIndex,
      Function.update] at hr
  all_goals
    rw [← hr]
    constructor <;> intro j hj <;> simp (disch := omega) only [Function.update_of_ne]

/-- The small branch saves the exponent and sign at exactly `k+12` and
`k+13`, so the entire higher caller area survives. -/
theorem proxy_prepare_frame {mag q : K} {k : ℕ} {s t : State K} (hq : q ≠ 0)
    (hp : s.pc = 24) (ho : s.output = none) (h₃ : s.data 3 = q) (hk : s.index 4 = k)
    (hs : s.index 5 = if mag < 1 then 1 else 0)
    (hr : runExactly logProxyProgram s (if mag < 1 then 23 else 22) = some t) :
    PreservesRegisters (k+14) 9 s t := by
  by_cases h : mag < 1 <;>
    simp (config := {maxSteps := 100000}) [runExactly, step, execInstr, hp, ho, h₃, hk, hs, h,
      hq, State.putData, State.putIndex, Function.update] at hr
  all_goals
    rw [← hr]
    constructor <;> intro j hj <;> simp (disch := omega) only [Function.update_of_ne]

/-- Neither indirect load changes its source; the only scalar destinations in
the restore block are zero, three and four. -/
theorem proxy_restore_frame {s : State K} (hp : s.pc = 115) (ho : s.output = none) :
    ∃ t, runExactly logProxyProgram s 6 = some t ∧ t.output = some 0 ∧
      PreservesRegisters 5 0 s t := by
  simp [runExactly, step, execInstr, hp, ho, State.putData, Function.update]
  constructor <;> intro j hj <;> simp (disch := omega) only [Function.update_of_ne]

end ProxyKernel

open ProxyKernel

private theorem framed_raw_halt (fuel k : ℕ) {mag : K} (hm : 0 < mag) (s : State K)
    (hpc : s.pc = 0) (ho : s.output = none) (hd0 : s.data 0 = mag)
    (hf0 : s.index 0 = fuel) (hk0 : s.index 1 = k) :
    ∃ n t, runExactly logProxyProgram s n = some t ∧ t.output ≠ none ∧
      PreservesRegisters (max (8+fuel) (k+14)) 9 s t := by
  let D := max (8+fuel) (k+14)
  have dRange : 8+fuel ≤ D := le_max_left _ _
  have dPrep : k+14 ≤ D := le_max_right _ _
  obtain ⟨u, hu, upc, uo, udata, ufuel, uk, usign⟩ :=
    proxy_prefix_run_exact fuel k mag s hpc ho hd0 hf0 hk0
  have F₁ : PreservesRegisters D 9 s u :=
    (proxy_prefix_frame hpc ho hd0 hu).weaken (by omega) (by decide)
  let a := {u with pc := 0}
  have reset : stateAt 6 a = u := by cases u; simp_all [a, stateAt]
  obtain ⟨j, _, v, hv, vo, branch⟩ := range_run_until_halt fuel hm a rfl uo udata ufuel
  have relocated := relocate_run 6 false proxy_range_lookup hv (Or.inr vo)
  rw [reset] at relocated
  have rawPrefix := proxy_join hu relocated
  have F₂ : PreservesRegisters D 9 u (stateAt 6 v) := by
    change PreservesRegisters D 9 a v
    exact (logRangeProgram_frame fuel hm a rfl uo udata ufuel hv).weaken dRange (by decide)
  have Fbase := F₁.trans F₂
  have h4 : v.index 4 = k := (range_preserves_index hv (by decide : 4 ≤ 4)).trans uk
  have h5 : v.index 5 = if mag < 1 then 1 else 0 :=
    (range_preserves_index hv (by decide : 4 ≤ 5)).trans usign
  cases hanswer : rangeAnswer fuel (normalizedRangeInput mag) 2 with
  | none =>
    rw [hanswer] at branch
    let t := {(stateAt 6 v) with output := some 1}
    have endRun : runExactly logProxyProgram (stateAt 6 v) 1 = some t := by
      simp [runExactly, step, stateAt, branch, vo, fetch_large_halt, execInstr, t]
    exact ⟨_, t, proxy_join rawPrefix endRun, by simp [t], Fbase⟩
  | some pair =>
    rcases pair with ⟨e,q⟩
    rw [hanswer] at branch
    obtain ⟨vp,v0,v3,v4⟩ := branch
    let mag' := normalizedRangeInput mag
    let mid := mag'/q
    have hnorm : normalizedRangeInput mag = RealProxy.normalizedMagnitude mag := by
      by_cases h : mag < 1 <;> simp [normalizedRangeInput, RealProxy.normalizedMagnitude, h]
    have hz : 1 ≤ mag' := by
      change 1 ≤ normalizedRangeInput mag
      rw [hnorm]
      exact RealProxy.one_le_normalizedMagnitude hm
    have hspec := (RealProxy.powerSearch_spec fuel mag' (2:K) hz (by norm_num)).2
    have hresult : (RealProxy.powerSearch fuel mag' 2).answer = some (e,q) :=
      (rangeAnswer_field_eq fuel mag' 2).symm.trans hanswer
    rw [hresult] at hspec
    obtain ⟨hq, hqle, _, _⟩ := hspec
    have hqpos : 0 < q := hq ▸ pow_pos (by norm_num) _
    have hmid : 1 ≤ mid := (one_le_div hqpos).mpr hqle
    have hp24 : (stateAt 6 v).pc = 24 := by simp [stateAt, vp]
    obtain ⟨w, hw, wp, wo, w0, wk, _, _, _, _⟩ := prepare_run_exact k e mag q hqpos.ne'
      (stateAt 6 v) hp24 vo v0 v3 v4 h4 h5
    have F₃ : PreservesRegisters D 9 (stateAt 6 v) w :=
      (proxy_prepare_frame hqpos.ne' hp24 vo v3 h4 h5 hw).weaken dPrep le_rfl
    let b := {w with pc := 0}
    have reset' : stateAt 56 b = w := by cases w; simp_all [b, stateAt]
    obtain ⟨x, hx, xp, xo, _, _, F⟩ := mantissaProgram_run_until_halt hmid k b rfl wo w0 wk
    have relocated' := relocate_run 56 false proxy_mantissa_lookup hx (Or.inr xo)
    rw [reset'] at relocated'
    have F₄ : PreservesRegisters D 9 w (stateAt 56 x) := by
      change PreservesRegisters D 9 b x
      exact F.weaken (by omega) (by decide)
    obtain ⟨out, hfinal, htag, F₅⟩ := proxy_restore_frame (s := stateAt 56 x)
      (by simp [stateAt, xp]) xo
    have hrun := proxy_join (proxy_join (proxy_join rawPrefix hw) relocated') hfinal
    exact ⟨_, out, hrun, by simp [htag],
      Fbase.trans (F₃.trans (F₄.trans (F₅.weaken (by omega) (by decide))))⟩

/-- A deterministic run cannot continue past a state that already halted. -/
theorem runExactly_le_of_halted {p : Program} {s t u : State K} {m n : ℕ}
    (ht : runExactly p s m = some t) (ho : t.output ≠ none)
    (hu : runExactly p s n = some u) : n ≤ m := by
  by_contra! hg
  have hn : 0 < n-m := by omega
  rw [show n = m+(n-m) by omega, runExactly_add_series, ht, Option.bind_some] at hu
  obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [hj, runExactly_succ_first] at hu
  cases he : t.output with
  | none => exact ho he
  | some tag => simp [step, he] at hu

/-- The physical caller area at a completed raw proxy call begins above both
the range stack and the two saved mantissa slots. Both the symbolic and the
explicit branch meet the same footprint. -/
theorem logProxyProgram_frame_halted (fuel k : ℕ) {mag : K} (hm : 0 < mag) (s : State K)
    (hp : s.pc = 0) (ho : s.output = none) (hd : s.data 0 = mag)
    (hf : s.index 0 = fuel) (hk : s.index 1 = k) {n : ℕ} {t : State K}
    (ht : runExactly logProxyProgram s n = some t) (hhalt : t.output ≠ none) :
    PreservesRegisters (max (8+fuel) (k+14)) 9 s t := by
  obtain ⟨j,u,hu,hstop,F⟩ := framed_raw_halt fuel k hm s hp ho hd hf hk
  have eq : n = j := Nat.le_antisymm (runExactly_le_of_halted hu hstop ht)
    (runExactly_le_of_halted ht hhalt hu)
  rw [eq] at ht
  rw [Option.some.inj (ht.symm.trans hu)]
  exact F

/-- The same physical frame holds at the live halt instruction, allowing the
caller to replace it by a jump to its continuation. -/
theorem logProxyProgram_frame_before_halt (fuel k : ℕ) {mag : K} (hm : 0 < mag) (s : State K)
    (hp : s.pc = 0) (ho : s.output = none) (hd : s.data 0 = mag)
    (hf : s.index 0 = fuel) (hk : s.index 1 = k) {n tag : ℕ} {t : State K}
    (ht : runExactly logProxyProgram s n = some t) (hlive : t.output = none)
    (hfetch : logProxyProgram[t.pc]? = some (.halt tag)) :
    PreservesRegisters (max (8+fuel) (k+14)) 9 s t := by
  let u := {t with output := some tag}
  have hnext : step logProxyProgram t = some u := by simp [step, hlive, hfetch, execInstr, u]
  have extended : runExactly logProxyProgram s (n+1) = some u := by
    rw [runExactly, ht, Option.bind_some]; exact hnext
  have F := logProxyProgram_frame_halted fuel k hm s hp ho hd hf hk extended (by simp [u])
  exact F

end Compression
end LinearProgramming
end Optimization
end OAI
