import OAI.Optimization.LinearProgramming.Compression.ProxyRangeFrame
import OAI.Optimization.LinearProgramming.Compression.ProxyMantissaProgram
import OAI.Optimization.LinearProgramming.Compression.ProxyOracle

/-! The linked, uniform arithmetic RAM for one online logarithm proxy. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.RAM OAI.Optimization.LinearProgramming.FieldTransfer

def proxyCallInstr (base ret : ℕ) (op : Instr) : Instr :=
  if op = .halt 0 then .jump ret else rebaseInstr base op

private def proxyInit : Program :=
  [.addrCopy 4 1, .const 7 1, .branchLT 0 7 3 5, .addrConst 5 1, .jump 6, .addrConst 5 0]

private def smallSetup : Program := [.addrCopy 6 4] ++ List.replicate 12 (.incr 6 6) ++
  [.store 6 4, .incr 7 6, .addrConst 8 0, .branchAddrLT 8 5 50 52, .const 6 (-1), .jump 53,
   .const 6 1, .store 7 6, .div 0 0 3, .addrCopy 0 4]

private def proxyFinish : Program :=
  [.load 3 6, .load 4 7, .add 0 0 3, .mul 0 0 4, .halt 0]

private def throughRange : Program := proxyInit ++ logRangeProgram.map (proxyCallInstr 6 33)
private def throughSetup : Program := throughRange ++ smallSetup

/-- Inputs are one positive scalar magnitude and two constructed counters `[fuel,k]`.
Tag 1 retains a symbolic log. Tag 0 returns the signed rational proxy in scalar register
0; the grid digits for the fractional part occupy registers 8 through `k+9`. -/
def logProxyProgram : Program :=
  throughSetup ++ (mantissaProgram.map (proxyCallInstr 56 116) ++ proxyFinish)

theorem proxyCall_lookup {pre post callee : Program} {off ret i : ℕ}
    (hoff : pre.length = off) {op : Instr} (hi : callee[i]? = some op)
    (hn : false = true ∨ ∀ tag, op ≠ .halt tag) :
    (pre ++ (callee.map (proxyCallInstr off ret) ++ post))[off+i]? = some (rebaseInstr off op) := by
  have hlen : i < callee.length := (List.getElem?_eq_some_iff.mp hi).choose
  have hs : off + i - pre.length = i := by omega
  rw [List.getElem?_append_right (by omega), hs, List.getElem?_append_left (by simpa using hlen),
    List.getElem?_map, hi]
  have hh : op ≠ .halt 0 := by
    rcases hn with h | h
    · contradiction
    · exact h 0
  simp [proxyCallInstr,hh]

namespace ProxyKernel

theorem proxy_range_lookup (i : ℕ) (op : Instr) (hi : logRangeProgram[i]? = some op)
    (hn : false = true ∨ ∀ tag, op ≠ .halt tag) :
    logProxyProgram[6+i]? = some (rebaseInstr 6 op) := by
  simpa only [logProxyProgram, throughSetup, throughRange, List.append_assoc] using
    (proxyCall_lookup (off := 6) (pre := proxyInit) (post := smallSetup ++ (mantissaProgram.map (proxyCallInstr 56 116) ++ proxyFinish))
      (ret := 33) rfl hi hn)

theorem proxy_mantissa_lookup (i : ℕ) (op : Instr) (hi : mantissaProgram[i]? = some op)
    (hn : false = true ∨ ∀ tag, op ≠ .halt tag) :
    logProxyProgram[56+i]? = some (rebaseInstr 56 op) :=
  proxyCall_lookup (pre := throughSetup) (post := proxyFinish) (ret := 116) rfl hi hn

/- The interface addresses appearing in actual traces reduce independently of the bodies
of the two linked kernels. -/
@[local simp] theorem fetch0 : logProxyProgram[0]? = some (.addrCopy 4 1) := rfl
@[local simp] theorem fetch1 : logProxyProgram[1]? = some (.const 7 1) := rfl
@[local simp] theorem fetch2 : logProxyProgram[2]? = some (.branchLT 0 7 3 5) := rfl
@[local simp] theorem fetch3 : logProxyProgram[3]? = some (.addrConst 5 1) := rfl
@[local simp] theorem fetch4 : logProxyProgram[4]? = some (.jump 6) := rfl
@[local simp] theorem fetch5 : logProxyProgram[5]? = some (.addrConst 5 0) := rfl
@[local simp] theorem fetch33 : logProxyProgram[33]? = some (.addrCopy 6 4) := rfl
@[local simp] theorem fetch34 : logProxyProgram[34]? = some (.incr 6 6) := rfl
@[local simp] theorem fetch35 : logProxyProgram[35]? = some (.incr 6 6) := rfl
@[local simp] theorem fetch36 : logProxyProgram[36]? = some (.incr 6 6) := rfl
@[local simp] theorem fetch37 : logProxyProgram[37]? = some (.incr 6 6) := rfl
@[local simp] theorem fetch38 : logProxyProgram[38]? = some (.incr 6 6) := rfl
@[local simp] theorem fetch39 : logProxyProgram[39]? = some (.incr 6 6) := rfl
@[local simp] theorem fetch40 : logProxyProgram[40]? = some (.incr 6 6) := rfl
@[local simp] theorem fetch41 : logProxyProgram[41]? = some (.incr 6 6) := rfl
@[local simp] theorem fetch42 : logProxyProgram[42]? = some (.incr 6 6) := rfl
@[local simp] theorem fetch43 : logProxyProgram[43]? = some (.incr 6 6) := rfl
@[local simp] theorem fetch44 : logProxyProgram[44]? = some (.incr 6 6) := rfl
@[local simp] theorem fetch45 : logProxyProgram[45]? = some (.incr 6 6) := rfl
@[local simp] theorem fetch46 : logProxyProgram[46]? = some (.store 6 4) := rfl
@[local simp] theorem fetch47 : logProxyProgram[47]? = some (.incr 7 6) := rfl
@[local simp] theorem fetch48 : logProxyProgram[48]? = some (.addrConst 8 0) := rfl
@[local simp] theorem fetch49 : logProxyProgram[49]? = some (.branchAddrLT 8 5 50 52) := rfl
@[local simp] theorem fetch50 : logProxyProgram[50]? = some (.const 6 (-1)) := rfl
@[local simp] theorem fetch51 : logProxyProgram[51]? = some (.jump 53) := rfl
@[local simp] theorem fetch52 : logProxyProgram[52]? = some (.const 6 1) := rfl
@[local simp] theorem fetch53 : logProxyProgram[53]? = some (.store 7 6) := rfl
@[local simp] theorem fetch54 : logProxyProgram[54]? = some (.div 0 0 3) := rfl
@[local simp] theorem fetch55 : logProxyProgram[55]? = some (.addrCopy 0 4) := rfl
@[local simp] theorem fetch116 : logProxyProgram[116]? = some (.load 3 6) := rfl
@[local simp] theorem fetch117 : logProxyProgram[117]? = some (.load 4 7) := rfl
@[local simp] theorem fetch118 : logProxyProgram[118]? = some (.add 0 0 3) := rfl
@[local simp] theorem fetch119 : logProxyProgram[119]? = some (.mul 0 0 4) := rfl
@[local simp] theorem fetch120 : logProxyProgram[120]? = some (.halt 0) := rfl

theorem fetch_large_halt : logProxyProgram[17]? = some (.halt 1) := rfl
theorem fetch_small_jump : logProxyProgram[24]? = some (.jump 33) := rfl
theorem fetch_restore_jump : logProxyProgram[115]? = some (.jump 116) := rfl

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem proxy_prefix_run_exact (fuel k : ℕ) (mag : K) (a : State K)
    (hpc : a.pc = 0) (ho : a.output = none) (hd : a.data 0 = mag)
    (hf : a.index 0 = fuel) (hk : a.index 1 = k) :
    ∃ s, runExactly logProxyProgram a (if mag < 1 then 5 else 4) = some s ∧
      s.pc = 6 ∧ s.output = none ∧ s.data 0 = mag ∧ s.index 0 = fuel ∧ s.index 4 = k ∧
      s.index 5 = (if mag < 1 then 1 else 0) := by
  by_cases h : mag < 1
  · simp [runExactly,step,execInstr,hpc,ho,hd,hf,hk,
      State.putData,State.putIndex,Function.update,h]
  · simp [runExactly,step,execInstr,hpc,ho,hd,hf,hk,
      State.putData,State.putIndex,Function.update,h]

theorem proxy_prefix_run (fuel k : ℕ) (mag : K) (a : State K)
    (hpc : a.pc = 0) (ho : a.output = none) (hd : a.data 0 = mag)
    (hf : a.index 0 = fuel) (hk : a.index 1 = k) :
    ∃ ell ≤ 5, ∃ s, runExactly logProxyProgram a ell = some s ∧
      s.pc = 6 ∧ s.output = none ∧ s.data 0 = mag ∧ s.index 0 = fuel ∧ s.index 4 = k ∧
      s.index 5 = (if mag < 1 then 1 else 0) := by
  obtain ⟨s, hrun, post⟩ := proxy_prefix_run_exact fuel k mag a hpc ho hd hf hk
  exact ⟨_, by split <;> decide, s, hrun, post⟩

theorem prepare_run_exact (k e : ℕ) (mag q : K) (hq : q ≠ 0) (s : State K)
    (hpc : s.pc = 24) (hgo : s.output = none) (h₀ : s.data 0 = normalizedRangeInput mag)
    (h₃ : s.data 3 = q) (h₄ : s.data 4 = (e : K)) (hk : s.index 4 = k)
    (hs : s.index 5 = if mag < 1 then 1 else 0) :
    ∃ t, runExactly logProxyProgram s (if mag < 1 then 23 else 22) = some t ∧
      t.pc = 56 ∧ t.output = none ∧ t.data 0 = normalizedRangeInput mag / q ∧
      t.index 0 = k ∧ t.index 6 = k+12 ∧ t.index 7 = k+13 ∧
      t.data (k+12) = (e : K) ∧ t.data (k+13) = (if mag < 1 then -1 else 1) := by
  by_cases h : mag < 1
  · simp (config := {maxSteps := 100000}) [runExactly, step, execInstr,
      fetch_small_jump, hpc, hgo, h₀, h₃, h₄, hk, hs, h,
      State.putData, State.putIndex, Function.update, hq]
  · simp (config := {maxSteps := 100000}) [runExactly, step, execInstr,
      fetch_small_jump, hpc, hgo, h₀, h₃, h₄, hk, hs, h,
      State.putData, State.putIndex, Function.update, hq]

theorem prepare_run (k e : ℕ) (mag q : K) (hq : q ≠ 0) (s : State K)
    (hpc : s.pc = 24) (hgo : s.output = none) (h₀ : s.data 0 = normalizedRangeInput mag)
    (h₃ : s.data 3 = q) (h₄ : s.data 4 = (e : K)) (hk : s.index 4 = k)
    (hs : s.index 5 = if mag < 1 then 1 else 0) :
    ∃ ell ≤ 23, ∃ t, runExactly logProxyProgram s ell = some t ∧
      t.pc = 56 ∧ t.output = none ∧ t.data 0 = normalizedRangeInput mag / q ∧
      t.index 0 = k ∧ t.index 6 = k+12 ∧ t.index 7 = k+13 ∧
      t.data (k+12) = (e : K) ∧ t.data (k+13) = (if mag < 1 then -1 else 1) := by
  obtain ⟨t, hrun, post⟩ := prepare_run_exact k e mag q hq s hpc hgo h₀ h₃ h₄ hk hs
  exact ⟨_, by split <;> decide, t, hrun, post⟩

theorem restore_run (k : ℕ) (e : ℕ) (frac sign : K) (s : State K)
    (hpc : s.pc = 115) (hgo : s.output = none) (hfrac : s.data 0 = frac)
    (h₆ : s.index 6 = k+12) (h₇ : s.index 7 = k+13) (he : s.data (k+12) = (e : K))
    (hsign : s.data (k+13) = sign) :
    ∃ t, runExactly logProxyProgram s 6 = some t ∧ t.output = some 0 ∧
      t.data 0 = (frac + e)*sign ∧ ∀ j < k+2, t.data (8+j) = s.data (8+j) := by
  simp [runExactly,step,execInstr,fetch_restore_jump, hpc,hgo,hfrac,h₆,h₇,he,hsign,State.putData,Function.update]
  intro j _
  split_ifs <;> first | rfl | omega

theorem proxy_join {a b c : State K} {i j : ℕ}
    (ha : runExactly logProxyProgram a i = some b) (hb : runExactly logProxyProgram b j = some c) :
    runExactly logProxyProgram a (i+j) = some c := by
  rw [runExactly_add_series,ha,Option.bind_some]
  exact hb

end ProxyKernel

open ProxyKernel

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Field-generic behavior of the complete executable proxy generator. Large inputs keep
their symbolic representation. Other inputs return the signed integer part plus the dyadic
mantissa. The run produces every grid bit by comparisons in its own registers. -/
theorem logProxyProgram_trace_from (fuel k : ℕ) {mag : K} (hm : 0 < mag) (input : State K)
    (pc0 : input.pc = 0) (live : input.output = none) (input0 : input.data 0 = mag)
    (ifuel : input.index 0 = fuel) (ik : input.index 1 = k) :
    ∃ ell ≤ 16*fuel+27*k+210, ∃ t : Fin (ell+1) → State K,
      Trace logProxyProgram input ell t ∧
      (match rangeAnswer fuel (normalizedRangeInput mag) 2 with
       | none => (t (Fin.last _)).output = some 1
       | some (e,q) =>
         let z := normalizedRangeInput mag / q
         let bits := mantissaGridNumerator z k
         (t (Fin.last _)).output = some 0 ∧
         (t (Fin.last _)).data 0 = ((bits.1 : K) / 2^(k+2) + e) * (if mag < 1 then -1 else 1) ∧
         ∀ j < k+2, (t (Fin.last _)).data (8+j) =
           ((gridDigit (logTruncation z (k+6) / logTruncation (2 : K) (k+6)) j).toNat : K)) := by
  obtain ⟨i,hi,s,hs,hpc,hgo,hd,hf,hk,hsg⟩ := proxy_prefix_run fuel k mag input pc0 live input0 ifuel ik
  let a := {s with pc := 0}
  have ha : stateAt 6 a = s := by cases s; simp_all [stateAt,a]
  obtain ⟨j,hj,u,hu,hulive,hret⟩ := range_run_until_halt fuel hm a rfl hgo hd hf
  have h4 : u.index 4 = k := (range_preserves_index hu (by decide : 4 ≤ 4)).trans hk
  have h5 : u.index 5 = (if mag < 1 then 1 else 0) :=
    (range_preserves_index hu (by decide : 4 ≤ 5)).trans hsg
  have hrel := relocate_run 6 false proxy_range_lookup hu (Or.inr hulive)
  rw [ha] at hrel
  have hupart := proxy_join hs hrel
  cases hanswer : rangeAnswer fuel (normalizedRangeInput mag) 2 with
  | none =>
    rw [hanswer] at hret
    have hlast : runExactly logProxyProgram (stateAt 6 u) 1 =
        some {(stateAt 6 u) with output := some 1} := by
      simp [runExactly,step,stateAt,hret,hulive,fetch_large_halt,execInstr]
    obtain ⟨t,ht,hend⟩ := (runExactly_iff_trace _).mp (proxy_join hupart hlast)
    exact ⟨i+j+1, by omega, t, ht, hend ▸ rfl⟩
  | some pair =>
    rcases pair with ⟨e,q⟩
    rw [hanswer] at hret
    obtain ⟨huPC,hu0,hu3,hu4⟩ := hret
    let mag' := normalizedRangeInput mag
    let mid := mag' / q
    have hnorm : normalizedRangeInput mag = RealProxy.normalizedMagnitude mag := by
      by_cases h : mag < 1 <;> simp [normalizedRangeInput,RealProxy.normalizedMagnitude,h]
    have hz : 1 ≤ mag' := by
      change 1 ≤ normalizedRangeInput mag
      rw [hnorm]
      exact RealProxy.one_le_normalizedMagnitude hm
    have hpow := (RealProxy.powerSearch_spec fuel mag' (2 : K) hz (by norm_num)).2
    have hanswer' : (RealProxy.powerSearch fuel mag' 2).answer = some (e,q) :=
      (rangeAnswer_field_eq fuel mag' 2).symm.trans hanswer
    rw [hanswer'] at hpow
    obtain ⟨hq, hqle, _, _⟩ := hpow
    have hqpos : 0 < q := hq ▸ pow_pos (by norm_num) _
    have hmid : 1 ≤ mid := (one_le_div hqpos).mpr hqle
    obtain ⟨l,hl,v,hv,vpc,vgo,v0,vk,v6,v7,vexp,vsign⟩ := prepare_run k e mag q hqpos.ne'
      (stateAt 6 u) (by simp [stateAt,huPC]) hulive hu0 hu3 hu4 h4 h5
    let b := {v with pc := 0}
    have hb : stateAt 56 b = v := by cases v; simp_all [stateAt,b]
    obtain ⟨w,hw,wpc,wgo,w0,wbits,hframe⟩ :=
      mantissaProgram_run_until_halt hmid k b rfl vgo v0 vk
    have hwrel := relocate_run 56 false proxy_mantissa_lookup hw (Or.inr wgo)
    rw [hb] at hwrel
    have w6 : w.index 6 = k+12 := (hframe.2 _ le_rfl).trans v6
    have w7 : w.index 7 = k+13 := (hframe.2 _ (by decide)).trans v7
    have we : w.data (k+12) = (e : K) := (hframe.1 _ le_rfl).trans vexp
    have ws : w.data (k+13) = (if mag < 1 then -1 else 1) :=
      (hframe.1 _ (by omega)).trans vsign
    obtain ⟨out, hdone, otag, oval, obits⟩ := restore_run k e
      (((mantissaGridNumerator mid k).1 : K) / 2^(k+2)) (if mag < 1 then -1 else 1)
      (stateAt 56 w) (by simp [stateAt,wpc]) wgo w0 w6 w7 we ws
    have hr := proxy_join (proxy_join (proxy_join hupart hv) hwrel) hdone
    obtain ⟨t,ht,hend⟩ := (runExactly_iff_trace _).mp hr
    refine ⟨i+j+l+(27*k+160)+6, by omega, t, ht, ?_⟩
    rw [hend]
    exact ⟨otag, oval, fun a ha => (obits a ha).trans (wbits a ha)⟩

/-- The complete proxy program from its standard pair of input counters. -/
theorem logProxyProgram_trace (fuel k : ℕ) {mag : K} (hm : 0 < mag) :
    ∃ ell ≤ 16*fuel+27*k+210, ∃ t : Fin (ell+1) → State K,
      Trace logProxyProgram (start [fuel,k] [mag]) ell t ∧
      (match rangeAnswer fuel (normalizedRangeInput mag) 2 with
       | none => (t (Fin.last _)).output = some 1
       | some (e,q) =>
         let z := normalizedRangeInput mag / q
         let bits := mantissaGridNumerator z k
         (t (Fin.last _)).output = some 0 ∧
         (t (Fin.last _)).data 0 = ((bits.1 : K) / 2^(k+2) + e) * (if mag < 1 then -1 else 1) ∧
         ∀ j < k+2, (t (Fin.last _)).data (8+j) =
           ((gridDigit (logTruncation z (k+6) / logTruncation (2 : K) (k+6)) j).toNat : K)) :=
  logProxyProgram_trace_from fuel k hm (start [fuel,k] [mag]) rfl rfl
    (by simp [start]) (by simp [start]) (by simp [start])

/-- Restoring the sign and integer part gives the single signed numerator represented
by the gridded value, over any ordered field. -/
theorem signed_grid_value (D e n : ℕ) (hD : D ≠ 0) (P : Prop) [Decidable P] :
    ((n : K)/D + e) * (if P then -1 else 1) =
      ((if P then -((D*e+n : ℕ) : ℤ) else ((D*e+n : ℕ) : ℤ) : ℤ) : K) / D := by
  let v := D*e+n
  have hc : ((v : ℤ) : K) = (D : K)*e+n := calc
    _ = (v : K) := Int.cast_natCast _
    _ = _ := by simp [v]
  have hn : (D : K) ≠ 0 := by exact_mod_cast hD
  by_cases h : P
  · simp only [ite_eq_left h, Int.cast_neg]
    change ((n : K) / D + e) * -1 = -((v : ℤ) : K) / D
    rw [hc]
    field_simp
    ring
  · simp only [ite_eq_right h]
    change ((n : K) / D + e) * 1 = ((v : ℤ) : K) / D
    rw [hc]
    field_simp
    ring

/-- The output tag and scalar agree with the exact gridded-or-symbolic numerator used by
the rational sign oracle. Every case is executed by the same finite RAM program. -/
theorem logProxyProgram_exec_from (fuel k : ℕ) {mag : ℚ} (hm : 0 < mag) (input : State ℚ)
    (pc0 : input.pc = 0) (live : input.output = none) (input0 : input.data 0 = mag)
    (ifuel : input.index 0 = fuel) (ik : input.index 1 = k) :
    ∃ ell ≤ 16*fuel+27*k+210, ∃ t : Fin (ell+1) → State ℚ,
      Trace logProxyProgram input ell t ∧
      (match logProxyNumerator fuel k mag with
       | none => (t (Fin.last _)).output = some 1
       | some u => (t (Fin.last _)).output = some 0 ∧
           (t (Fin.last _)).data 0 = (u : ℚ) / 2^(k+2)) := by
  obtain ⟨ell,hell,t,ht,hout⟩ := logProxyProgram_trace_from fuel k hm input pc0 live input0 ifuel ik
  refine ⟨ell,hell,t,ht,?_⟩
  have hn : normalizedRangeInput mag = normalizedMagnitude mag := by
    by_cases h : mag < 1 <;> simp [normalizedRangeInput, normalizedMagnitude, h]
  rw [hn,rangeAnswer_rat_eq] at hout
  by_cases hs : (powerSearch fuel (normalizedMagnitude mag) 2).answer = none
  · have hdata : logProxyNumerator fuel k mag = none := by simp only [logProxyNumerator,hs]
    rw [hdata]
    simpa only [hs] using hout
  · have hh : ∃ e q, (powerSearch fuel (normalizedMagnitude mag) 2).answer = some (e,q) := by
      rcases he : (powerSearch fuel (normalizedMagnitude mag) 2).answer with _ | ⟨e,q⟩
      · exact (hs he).elim
      · exact ⟨e,q,rfl⟩
    obtain ⟨e,q,he⟩ := hh
    rw [he] at hout
    obtain ⟨ho,hv,_⟩ := hout
    simp only [logProxyNumerator,he]
    refine ⟨ho,?_⟩
    rw [hv]
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      signed_grid_value (K := ℚ) (2^(k+2)) e (mantissaGridNumerator (normalizedMagnitude mag/q) k).1
        (by positivity) (mag < 1)

/-- The complete verified rational generator on its canonical input tape. -/
theorem logProxyProgram_exec (fuel k : ℕ) {mag : ℚ} (hm : 0 < mag) :
    ∃ ell ≤ 16*fuel+27*k+210, ∃ t : Fin (ell+1) → State ℚ,
      Trace logProxyProgram (start [fuel,k] [mag]) ell t ∧
      (match logProxyNumerator fuel k mag with
       | none => (t (Fin.last _)).output = some 1
       | some u => (t (Fin.last _)).output = some 0 ∧
           (t (Fin.last _)).data 0 = (u : ℚ) / 2^(k+2)) :=
  logProxyProgram_exec_from fuel k hm (start [fuel,k] [mag]) rfl rfl
    (by simp [start]) (by simp [start]) (by simp [start])

end Compression
end LinearProgramming
end Optimization
end OAI
