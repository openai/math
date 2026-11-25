import OAI.Optimization.LinearProgramming.Compression.ProxyProgram
import OAI.Optimization.LinearProgramming.Compression.ProxyKernelLayout

/-! The three scalar loads of the raw logarithm kernel read only its own working area. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.RAM OAI.Optimization.LinearProgramming.FieldTransfer ProxyKernel

variable {K : Type*} [LinearOrder K]

private def RawAddressInvariant (fuel k : ℕ) (s : State K) : Prop :=
  (s.pc = 0 → s.index 1 = k) ∧
  (s.pc ≤ 14 → s.index 0 = fuel) ∧
  (s.pc = 14 → s.index 2 = 8) ∧
  (1 ≤ s.pc → s.pc ≤ 55 → s.index 4 = k) ∧
  (15 ≤ s.pc → s.pc ≤ 32 → s.index 3+s.index 0 ≤ 8+fuel+(if s.pc=20 then 1 else 0)) ∧
  ((s.pc=18 ∨ s.pc=19 ∨ s.pc=20) → 0 < s.index 0) ∧
  (34 ≤ s.pc → s.pc ≤ 46 → s.index 6 = k+(s.pc-34)) ∧
  (47 ≤ s.pc → s.index 6 = k+12) ∧
  (48 ≤ s.pc → s.index 7 = k+13)

/-- Project a scalar-machine instruction onto just its control and address effects. -/
private def RawAddressEffect (op : Instr) (s t : State K) : Prop :=
  match op with
  | .addrConst d v => t.pc = s.pc+1 ∧ t.index = Function.update s.index d v
  | .addrCopy d a => t.pc = s.pc+1 ∧ t.index = Function.update s.index d (s.index a)
  | .incr d a => t.pc = s.pc+1 ∧ t.index = Function.update s.index d (s.index a+1)
  | .decr d a => t.pc = s.pc+1 ∧ t.index = Function.update s.index d (s.index a-1)
  | .addrLoad d a => t.pc = s.pc+1 ∧ t.index = Function.update s.index d (s.index (s.index a))
  | .addrStore a d => t.pc = s.pc+1 ∧ t.index = Function.update s.index (s.index a) (s.index d)
  | .branchLT a b yes no => t.pc = (if s.data a < s.data b then yes else no) ∧ t.index = s.index
  | .branchAddrLT a b yes no => t.pc = (if s.index a < s.index b then yes else no) ∧ t.index = s.index
  | .jump dest => t.pc = dest ∧ t.index = s.index
  | .halt _ => t.pc = s.pc ∧ t.index = s.index
  | _ => t.pc = s.pc+1 ∧ t.index = s.index

private theorem rawAddressEffect_sound [Field K] [IsStrictOrderedRing K] {op : Instr} {s t : State K}
    (h : execInstr op s = some t) : RawAddressEffect op s t := by
  cases op <;> simp only [execInstr] at h
  all_goals try split at h
  all_goals first | contradiction | (cases h; simp_all [RawAddressEffect, State.putData, State.putIndex])

attribute [local simp]
  fetch0 fetch1 fetch2 fetch3 fetch4 fetch5 fetch33 fetch34
  fetch35 fetch36 fetch37 fetch38 fetch39 fetch40 fetch41 fetch42
  fetch43 fetch44 fetch45 fetch46 fetch47 fetch48 fetch49 fetch50
  fetch51 fetch52 fetch53 fetch54 fetch55

@[local simp] private theorem rangePc6 : logProxyProgram[6]? = some (.const 1 1) := rfl
@[local simp] private theorem rangePc7 : logProxyProgram[7]? = some (.branchLT 0 1 8 9) := rfl
@[local simp] private theorem rangePc8 : logProxyProgram[8]? = some (.div 0 1 0) := rfl
@[local simp] private theorem rangePc9 : logProxyProgram[9]? = some (.const 2 2) := rfl
@[local simp] private theorem rangePc10 : logProxyProgram[10]? = some (.copy 3 1) := rfl
@[local simp] private theorem rangePc11 : logProxyProgram[11]? = some (.const 4 0) := rfl
@[local simp] private theorem rangePc12 : logProxyProgram[12]? = some (.addrConst 1 0) := rfl
@[local simp] private theorem rangePc13 : logProxyProgram[13]? = some (.addrConst 2 8) := rfl
@[local simp] private theorem rangePc14 : logProxyProgram[14]? = some (.addrCopy 3 2) := rfl
@[local simp] private theorem rangePc15 : logProxyProgram[15]? = some (.branchLT 0 2 23 16) := rfl
@[local simp] private theorem rangePc16 : logProxyProgram[16]? = some (.branchAddrLT 1 0 18 17) := rfl
@[local simp] private theorem rangePc17 : logProxyProgram[17]? = some (.halt 1) := rfl
@[local simp] private theorem rangePc18 : logProxyProgram[18]? = some (.store 3 2) := rfl
@[local simp] private theorem rangePc19 : logProxyProgram[19]? = some (.incr 3 3) := rfl
@[local simp] private theorem rangePc20 : logProxyProgram[20]? = some (.decr 0 0) := rfl
@[local simp] private theorem rangePc21 : logProxyProgram[21]? = some (.mul 2 2 2) := rfl
@[local simp] private theorem rangePc22 : logProxyProgram[22]? = some (.jump 15) := rfl
@[local simp] private theorem rangePc23 : logProxyProgram[23]? = some (.branchAddrLT 2 3 25 24) := rfl
@[local simp] private theorem rangePc24 : logProxyProgram[24]? = some (.jump 33) := rfl
@[local simp] private theorem rangePc25 : logProxyProgram[25]? = some (.decr 3 3) := rfl
@[local simp] private theorem rangePc26 : logProxyProgram[26]? = some (.load 2 3) := rfl
@[local simp] private theorem rangePc27 : logProxyProgram[27]? = some (.mul 5 3 2) := rfl
@[local simp] private theorem rangePc28 : logProxyProgram[28]? = some (.add 4 4 4) := rfl
@[local simp] private theorem rangePc29 : logProxyProgram[29]? = some (.branchLT 0 5 23 30) := rfl
@[local simp] private theorem rangePc30 : logProxyProgram[30]? = some (.copy 3 5) := rfl
@[local simp] private theorem rangePc31 : logProxyProgram[31]? = some (.add 4 4 1) := rfl
@[local simp] private theorem rangePc32 : logProxyProgram[32]? = some (.jump 23) := rfl

set_option maxHeartbeats 1200000 in
private theorem raw_early_address_step (fuel k : ℕ) {s t : State K} (hpc : s.pc < 56)
    (hh : RawAddressInvariant fuel k s) {op : Instr} (hf : logProxyProgram[s.pc]? = some op)
    (hs : RawAddressEffect op s t) : RawAddressInvariant fuel k t := by
  interval_cases pc : s.pc <;> simp at hf <;> subst op
  all_goals rcases hs with ⟨hp, ha⟩
  all_goals try split at hp
  all_goals simp [RawAddressInvariant, pc] at hh
  all_goals simp [RawAddressInvariant, ha, hp, pc, Function.update]
  all_goals omega

private def suffixTargets (op : Instr) : Bool :=
  match op with
  | .branchLT _ _ x y | .branchAddrLT _ _ x y => decide (56 ≤ x ∧ 56 ≤ y)
  | .jump x => decide (56 ≤ x)
  | _ => true

private theorem suffix_effect {op : Instr} {s t : State K} (hpc : 56 ≤ s.pc)
    (hc : suffixTargets op = true ∧ addressWritesBelow 6 op = true)
    (hs : RawAddressEffect op s t) :
    56 ≤ t.pc ∧ t.index 6 = s.index 6 ∧ t.index 7 = s.index 7 := by
  cases op <;> simp [suffixTargets, addressWritesBelow] at hc <;>
    obtain ⟨hp, ha⟩ := hs <;> simp [hp, ha, Function.update]
  all_goals first | omega | (split_ifs <;> omega)

private theorem raw_late_address_step (fuel k : ℕ) {s t : State K} (hpc : 56 ≤ s.pc)
    (hh : RawAddressInvariant fuel k s) {op : Instr} (hf : logProxyProgram[s.pc]? = some op)
    (hs : RawAddressEffect op s t) : RawAddressInvariant fuel k t := by
  have checked : (logProxyProgram.drop 56).all (fun op => suffixTargets op && addressWritesBelow 6 op) = true := by decide
  have fetch : (logProxyProgram.drop 56)[s.pc-56]? = some op := by
    rw [List.getElem?_drop, show 56+(s.pc-56) = s.pc by omega]; exact hf
  have hc := List.all_eq_true.mp checked _ (List.mem_of_getElem? fetch)
  simp only [Bool.and_eq_true] at hc
  obtain ⟨hp,h6,h7⟩ := suffix_effect hpc hc hs
  obtain ⟨_,_,_,_,_,_,_,ptr6,ptr7⟩ := hh
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    fun _ => h6.trans (ptr6 (by omega)), fun _ => h7.trans (ptr7 (by omega))⟩

private theorem raw_address_step [Field K] [IsStrictOrderedRing K] (fuel k : ℕ) {s t : State K}
    (hh : RawAddressInvariant fuel k s) (hs : step logProxyProgram s = some t) :
    RawAddressInvariant fuel k t := by
  cases ho : s.output with
  | some tag => simp [step, ho] at hs
  | none =>
    cases hf : logProxyProgram[s.pc]? with
    | none => simp [step, ho, hf] at hs
    | some op =>
      have he := rawAddressEffect_sound (show execInstr op s = some t by simpa [step, ho, hf] using hs)
      by_cases h : s.pc < 56
      · exact raw_early_address_step fuel k h hh hf he
      · exact raw_late_address_step fuel k (by omega) hh hf he

private def rawLoadSite (pc : ℕ) : Option Instr → Bool
  | some (.load _ ptr) => decide ((pc=26 ∧ ptr=3) ∨ (pc=116 ∧ ptr=6) ∨ (pc=117 ∧ ptr=7))
  | _ => true

private def rawReadSites : ℕ → Program → Bool
  | _, [] => true
  | pc, op::ops => rawLoadSite pc (some op) && rawReadSites (pc+1) ops

private theorem rawReadSites_sound {p : Program} {off i : ℕ} {op : Instr}
    (hc : rawReadSites off p = true) (hf : p[i]? = some op) :
    rawLoadSite (off+i) (some op) = true := by
  induction p generalizing off i with
  | nil => simp at hf
  | cons head tail ih =>
    simp only [rawReadSites, Bool.and_eq_true] at hc
    cases i with
    | zero =>
      have eq : head = op := by simpa using hf
      simpa [eq] using hc.1
    | succ i =>
      have hr := ih hc.2 (by simpa using hf : tail[i]? = some op)
      rw [show off+i.succ = off+1+i by omega]
      exact hr

set_option maxRecDepth 16384 in
/-- At every state on either branch, scalar indirection stays below the range
stack limit or the saved exponent/sign pair. The caller may keep arbitrarily
large values in higher registers without affecting these loads. -/
theorem logProxyProgram_indirectReadBound [Field K] [IsStrictOrderedRing K] (fuel k : ℕ) (s : State K) (hp : s.pc = 0)
    (hf : s.index 0 = fuel) (hk : s.index 1 = k) {t : State K} {n : ℕ}
    (hr : runExactly logProxyProgram s n = some t) {dst ptr : ℕ}
    (hload : logProxyProgram[t.pc]? = some (.load dst ptr)) :
    t.index ptr < max (9+fuel) (k+14) := by
  have init : RawAddressInvariant fuel k s := by simp [RawAddressInvariant, hp, hf, hk]
  have budget {m : ℕ} {v : State K} (hv : runExactly logProxyProgram s m = some v) :
      RawAddressInvariant fuel k v := by
    induction m generalizing v with
    | zero => change some s = some v at hv; cases hv; exact init
    | succ m ih =>
      change (runExactly logProxyProgram s m).bind (step logProxyProgram) = some v at hv
      cases hu : runExactly logProxyProgram s m with
      | none => simp [hu] at hv
      | some u => exact raw_address_step fuel k (ih hu) (by simpa [hu] using hv)
  obtain ⟨_,_,_,_,stack,_,_,ptr6,ptr7⟩ := budget hr
  have codes : rawReadSites 0 logProxyProgram = true := by decide
  have sites : rawLoadSite t.pc (some (.load dst ptr)) = true := by
    simpa only [Nat.zero_add] using rawReadSites_sound codes hload
  have which := of_decide_eq_true sites
  rcases which with ⟨pc, rfl⟩ | ⟨pc,rfl⟩ | ⟨pc,rfl⟩
  · simp [pc] at stack
    omega
  · rw [ptr6 (by omega)]
    omega
  · rw [ptr7 (by omega)]
    omega

end Compression
end LinearProgramming
end Optimization
end OAI
