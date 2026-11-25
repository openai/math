import OAI.Optimization.LinearProgramming.Compression.ProxyProgram
import OAI.Optimization.LinearProgramming.Compression.ProxyRangeSafety
import OAI.Optimization.LinearProgramming.Compression.ProxyMantissaBits

/-! All-prefix rational register bounds for the fully linked logarithm proxy. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.RAM OAI.Optimization.LinearProgramming.FieldTransfer ProxyKernel

/-- The straight-line splice bounds are constants. Only the range and mantissa
kernels contribute parameter-dependent growth to this bound. -/
def proxyRegisterBound (B fuel k : ℕ) : ℕ :=
  let S := 10^5*(B+4)
  let R := rangeRegisterBound S fuel
  let P := 10^23*(R+4)
  let H := mantissaRegisterBound P k
  S+R+P+H+10^6*(H+4)+10*(R+4)

private theorem proxy_literals (d : ℕ) (r : ℚ) (hd : Instr.const d r ∈ logProxyProgram) :
    ratBits r ≤ 4 := by
  let good : Instr → Bool
    | .const _ q => decide (ratBits q ≤ 4)
    | _ => true
  have h : logProxyProgram.all good = true := by decide
  exact of_decide_eq_true (List.all_eq_true.mp h (.const d r) hd)

private theorem proxy_short {s t : State ℚ} {B j m : ℕ} (hs : scalarBound B s)
    (hj : j ≤ m) (hr : runExactly logProxyProgram s j = some t) :
    RegisterBoundedRun logProxyProgram s j t (10^m*(B+4)) := by
  have hh : scalarBound (B+4) s := fun i => (hs i).trans (by omega)
  exact (RegisterBoundedRun.short (B := B+4) (by omega)
    (fun d q hd => (proxy_literals d q hd).trans (by omega)) hh hr).weaken
    (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) hj))

/-- A complete legal program execution reaches a halt, with the bound at every
instruction, from any scratch state of the specified initial bit size. -/
theorem logProxyProgram_bounded_run (fuel k B : ℕ) {mag : ℚ} (hm : 0 < mag) (input : State ℚ)
    (pc0 : input.pc = 0) (live : input.output = none) (input0 : input.data 0 = mag)
    (ifuel : input.index 0 = fuel) (ik : input.index 1 = k) (hB : scalarBound B input) :
    ∃ ell ≤ 16*fuel+27*k+210, ∃ t tag, t.output = some tag ∧
      RegisterBoundedRun logProxyProgram input ell t (proxyRegisterBound B fuel k) := by
  let S := 10^5*(B+4)
  let R := rangeRegisterBound S fuel
  let P := 10^23*(R+4)
  let H := mantissaRegisterBound P k
  obtain ⟨i,hi,s,hs,hpc,hgo,hd,hf,hk,hsg⟩ := proxy_prefix_run fuel k mag input pc0 live input0 ifuel ik
  have bs : RegisterBoundedRun logProxyProgram input i s S := proxy_short hB hi hs
  let a := {s with pc := 0}
  have ha : stateAt 6 a = s := by cases s; simp_all [stateAt,a]
  obtain ⟨j,hj,u,hu,hulive,hret⟩ := range_run_until_halt fuel hm a rfl hgo hd hf
  have h4 : u.index 4 = k := (range_preserves_index hu (by decide : 4 ≤ 4)).trans hk
  have h5 : u.index 5 = (if mag < 1 then 1 else 0) :=
    (range_preserves_index hu (by decide : 4 ≤ 5)).trans hsg
  have br : RegisterBoundedRun logRangeProgram a j u R :=
    ⟨hu,fun _ _ _ hv => logRangeProgram_scalarBound hm fuel S a rfl hgo hd hf bs.finalBound hv⟩
  have brr := br.relocate 6 false proxy_range_lookup (Or.inr hulive)
  rw [ha] at brr
  have bp := bs.append brr
  cases hanswer : rangeAnswer fuel (normalizedRangeInput mag) 2 with
  | none =>
    rw [hanswer] at hret
    have hfetch : logProxyProgram[17]? = some (.halt 1) := rfl
    have hlast : runExactly logProxyProgram (stateAt 6 u) 1 =
        some {(stateAt 6 u) with output := some 1} := by
      simp [runExactly,step,stateAt,hret,hulive,hfetch,execInstr]
    have bend := bp.append (proxy_short brr.finalBound (le_refl 1) hlast)
    refine ⟨i+j+1,by omega,_,1,rfl,bend.weaken ?_⟩
    change S+R+10^1*(R+4) ≤ S+R+P+H+10^6*(H+4)+10*(R+4)
    omega
  | some pair =>
    rcases pair with ⟨e,q⟩
    rw [hanswer] at hret
    obtain ⟨upc,u0,u3,u4⟩ := hret
    let z := normalizedRangeInput mag
    let mid := z/q
    have hnorm : normalizedRangeInput mag = RealProxy.normalizedMagnitude mag := by
      by_cases h : mag < 1 <;> simp [normalizedRangeInput,RealProxy.normalizedMagnitude,h]
    have hz : 1 ≤ z := by change 1 ≤ normalizedRangeInput mag; rw [hnorm]; exact RealProxy.one_le_normalizedMagnitude hm
    have hpow := (RealProxy.powerSearch_spec fuel z (2:ℚ) hz (by norm_num)).2
    rw [(rangeAnswer_field_eq fuel z 2).symm.trans hanswer] at hpow
    obtain ⟨hq,hqle,_,_⟩ := hpow
    have hqp : 0 < q := hq ▸ pow_pos (by norm_num) _
    have hm1 : 1 ≤ mid := (one_le_div hqp).mpr hqle
    obtain ⟨l,hl,v,hv,vpc,vgo,v0,vk,v6,v7,ve,vs⟩ := prepare_run k e mag q hqp.ne' (stateAt 6 u)
      (by simp [stateAt,upc]) hulive u0 u3 u4 h4 h5
    have bv : RegisterBoundedRun logProxyProgram (stateAt 6 u) l v P := proxy_short brr.finalBound hl hv
    let b := {v with pc := 0}
    have hb : stateAt 56 b = v := by cases v; simp_all [stateAt,b]
    obtain ⟨w,hw,wpc,wgo,w0,_,hframe⟩ := mantissaProgram_run_until_halt hm1 k b rfl vgo v0 vk
    have bw : RegisterBoundedRun mantissaProgram b (27*k+160) w H :=
      ⟨hw,fun _ hdlen _ hwr => mantissaProgram_scalarBound hm1 k P b rfl vgo v0 vk bv.finalBound
        (by omega) hwr⟩
    have bwr := bw.relocate 56 false proxy_mantissa_lookup (Or.inr wgo)
    rw [hb] at bwr
    have w6 : w.index 6 = k+12 := (hframe.2 _ le_rfl).trans v6
    have w7 : w.index 7 = k+13 := (hframe.2 _ (by decide)).trans v7
    have we : w.data (k+12) = (e:ℚ) := (hframe.1 _ le_rfl).trans ve
    have ws : w.data (k+13) = (if mag < 1 then -1 else 1) := (hframe.1 _ (by omega)).trans vs
    obtain ⟨out, hdone, otag, _, _⟩ := restore_run k e
      (((mantissaGridNumerator mid k).1 : ℚ) / 2^(k+2)) (if mag < 1 then -1 else 1)
      (stateAt 56 w) (by simp [stateAt,wpc]) wgo w0 w6 w7 we ws
    have be := proxy_short bwr.finalBound (le_refl 6) hdone
    have full := ((bp.append bv).append bwr).append be
    refine ⟨i+j+l+(27*k+160)+6,by omega,out,0,otag,full.weaken ?_⟩
    change S+R+P+H+10^6*(H+4) ≤ S+R+P+H+10^6*(H+4)+10*(R+4)
    omega

theorem halted_no_successor (p : Program) (s : State ℚ) (n tag : ℕ) (h : s.output = some tag) :
    runExactly p s (n+1) = none := by
  induction n with
  | zero => simp [runExactly,step,h]
  | succ n ih =>
    change (runExactly p s (n+1)).bind (step p) = none
    exact congrArg (fun x => x.bind (step p)) ih

/-- Arbitrary input and scratch registers are allowed. Every state of every legal
execution satisfies one common encoding bound, independent of the actual branch. -/
theorem logProxyProgram_scalarBound (fuel k B : ℕ) {mag : ℚ} (hm : 0 < mag) (s : State ℚ)
    (pc0 : s.pc = 0) (live : s.output = none) (input0 : s.data 0 = mag)
    (ifuel : s.index 0 = fuel) (ik : s.index 1 = k) (hB : scalarBound B s)
    {n : ℕ} {v : State ℚ} (hvr : runExactly logProxyProgram s n = some v) :
    scalarBound (proxyRegisterBound B fuel k) v := by
  obtain ⟨ell,_,t,tag,ht,hr⟩ := logProxyProgram_bounded_run fuel k B hm s pc0 live input0 ifuel ik hB
  by_cases hle : n ≤ ell
  · exact hr.bound n hle v hvr
  · have hn : n = ell+(n-ell-1+1) := by omega
    rw [hn,runExactly_add_series,hr.execution,Option.bind_some,
      halted_no_successor logProxyProgram t _ tag ht] at hvr
    contradiction

end Compression
end LinearProgramming
end Optimization
end OAI
